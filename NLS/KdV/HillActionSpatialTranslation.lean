import NLS.KdV.HillSpatialTranslationDiscriminant
import NLS.KdV.HillActionHamiltonianField
import NLS.Poisson.GardnerSpatialTranslation

/-! Actual canonical actions have full complex translation-invariance germs
at every physical real source. Gardner covariance therefore transports the
ACTUAL action fields. The original physical real mean-zero translation
is a bounded isometric group, with its literal Fourier coefficients. -/
noncomputable section
open Set Complex Filter Topology Metric
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillHminusLabels_eq_of_discriminant_eq (p q : PeriodOneHminusOne)
    (hp : IsRealPeriodOneHminusOne p) (hq : IsRealPeriodOneHminusOne q)
    (hd : hillHminusDiscriminant p=hillHminusDiscriminant q) :
    hillHminusLabels p hp=hillHminusLabels q hq := by
  apply NLS.ordered_nat_enumeration_eq_of_multiplicity _ _
    (hillHminusLabels_finite_fiber p hp) (hillHminusLabels_finite_fiber q hq)
    (monotone_hillHminusLabels p hp) (monotone_hillHminusLabels q hq)
  intro x
  have he : hillHminusRadicand p=hillHminusRadicand q := by
    funext E
    simp only [hillHminusRadicand,hd]
  rw [hillHminusLabels_global_multiplicity,hillHminusLabels_global_multiplicity,he]

/-- Action invariance on the FULL physical real Hminus-one space, with no
zero-mean restriction or discarded low/closed gaps. -/
theorem hillHminusCanonicalAction_spatialTranslation_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (t : ℝ) (n : ℕ+) :
    hillHminusCanonicalAction n (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t q)=
      hillHminusCanonicalAction n q := by
  let T : PeriodOneHminusOne ≃ₗᵢ[ℂ] PeriodOneHminusOne :=
    WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t
  have hT : IsRealPeriodOneHminusOne (T q) := WeightedCoeff.spatialTranslation_real _ _ _ q hq
  have hd : hillHminusDiscriminant (T q)=hillHminusDiscriminant q :=
    funext (fun E => hillHminusDiscriminant_spatialTranslation q t E)
  have hl := hillHminusLabels_eq_of_discriminant_eq (T q) q hT hq hd
  have hp : hillHminusRealGapProfile (T q) (n:ℕ)=hillHminusRealGapProfile q (n:ℕ) := by
    funext E
    simp only [hillHminusRealGapProfile,hd]
  rw [hillHminusCanonicalAction_eq_real (T q) hT n,hillHminusCanonicalAction_eq_real q hq n]
  simp only [hillHminusCanonicalRealAction,hl,hp]

/-- ONE complex source ball precedes ALL actual action indices. The actual
translation-invariance equality holds throughout that ball, not merely at
the real center; this supplies the full cotangent transformation law. -/
theorem exists_hillHminusCanonicalActions_spatialTranslation_germ
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (t : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℕ+,
      EqOn (fun a => hillHminusCanonicalAction n
        (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t a))
        (hillHminusCanonicalAction n) (ball q ρ) := by
  let T : PeriodOneHminusOne →L[ℂ] PeriodOneHminusOne := (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t).toContinuousLinearEquiv.toContinuousLinearMap
  have hqD := real_mem_hillHminusCanonicalActionDomain q hq
  have htD := real_mem_hillHminusCanonicalActionDomain (T q)
    (WeightedCoeff.spatialTranslation_real _ _ _ q hq)
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_hillHminusCanonicalActionDomain.inter
      (isOpen_hillHminusCanonicalActionDomain.preimage T.continuous)).mem_nhds ⟨hqD,htD⟩)
  refine ⟨ρ,hρ,fun n => ?_⟩
  apply analytic_eqOn_of_real_periodOneHminus (ball q ρ) isOpen_ball (convex_ball q ρ).isPreconnected
    ⟨q,mem_ball_self hρ,hq⟩
  · intro a ha
    exact (analyticOnNhd_hillHminusCanonicalAction n (T a) (hball ha).2).comp (T.analyticAt a)
  · exact (analyticOnNhd_hillHminusCanonicalAction n).mono (fun a ha => (hball ha).1)
  · intro a _ ha
    exact hillHminusCanonicalAction_spatialTranslation_real a ha t n

/-- Exact spatial covariance of the ACTUAL action Hamiltonian vector at
EVERY physical real Hminus-one input, with its original Gardner tensor. -/
theorem hillHminusActionHamiltonianVector_spatialTranslation (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (t : ℝ) :
    hillHminusActionHamiltonianVector n
      (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t q)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t
        (hillHminusActionHamiltonianVector n q) := by
  obtain ⟨ρ,hρ,hEq⟩ := exists_hillHminusCanonicalActions_spatialTranslation_germ q hq t
  apply NLS.Poisson.gardnerHamiltonianVector_spatialTranslation_of_germ
  · exact (analyticOnNhd_hillHminusCanonicalAction n _
      (real_mem_hillHminusCanonicalActionDomain _ (WeightedCoeff.spatialTranslation_real _ _ _ q hq))).differentiableAt
  · filter_upwards [ball_mem_nhds q hρ] with a ha
    exact hEq n ha

/-- Literal bounded spatial translation on the actual physical real
mean-zero source. The projection is proved inactive on every input. -/
def hillRealSpatialTranslation (t : ℝ) : HillRealMeanZeroSource →L[ℝ] HillRealMeanZeroSource :=
  hillRealMeanZeroProjection.comp
    (((WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
      hillRealMeanZeroInclusion)

theorem hillRealSpatialTranslation_inclusion (t : ℝ) (q : HillRealMeanZeroSource) :
    hillRealMeanZeroInclusion (hillRealSpatialTranslation t q)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t (hillRealMeanZeroInclusion q) := by
  apply hillRealMeanZeroProjection_inclusion
  · exact WeightedCoeff.spatialTranslation_real _ _ _ _ q.property
  · change (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t
      (hillRealMeanZeroInclusion q)).val 0=0
    rw [WeightedCoeff.spatialTranslation_apply]
    change exp _ * q.val.val.val 0=0
    rw [show q.val.val.val 0=0 from q.val.property,mul_zero]

theorem norm_hillRealSpatialTranslation (t : ℝ) (q : HillRealMeanZeroSource) :
    ‖hillRealSpatialTranslation t q‖=‖q‖ := by
  change ‖hillRealMeanZeroInclusion (hillRealSpatialTranslation t q)‖=‖hillRealMeanZeroInclusion q‖
  rw [hillRealSpatialTranslation_inclusion]
  exact (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t).norm_map _

theorem hillRealSpatialTranslation_zero (q : HillRealMeanZeroSource) : hillRealSpatialTranslation 0 q=q := by
  apply hillRealMeanZeroInclusion_injective
  rw [hillRealSpatialTranslation_inclusion,WeightedCoeff.spatialTranslation_zero]

theorem hillRealSpatialTranslation_add (t s : ℝ) (q : HillRealMeanZeroSource) :
    hillRealSpatialTranslation t (hillRealSpatialTranslation s q)=hillRealSpatialTranslation (t+s) q := by
  apply hillRealMeanZeroInclusion_injective
  rw [hillRealSpatialTranslation_inclusion,hillRealSpatialTranslation_inclusion,
    hillRealSpatialTranslation_inclusion,WeightedCoeff.spatialTranslation_add]

/-- Physical period one gives the EXACT source translation period, with
no statement about the periods of the separate action Hamiltonian flows. -/
theorem hillRealSpatialTranslation_one (q : HillRealMeanZeroSource) : hillRealSpatialTranslation 1 q=q := by
  apply hillRealMeanZeroInclusion_injective
  rw [hillRealSpatialTranslation_inclusion]
  apply Subtype.ext
  funext k
  rw [WeightedCoeff.spatialTranslation_apply]
  have he : exp ((1*(2*Real.pi*k):ℝ)*I)=1 := by
    convert Complex.exp_int_mul_two_pi_mul_I k using 1
    congr 1
    push_cast
    ring
  rw [he,one_mul]

theorem hillRealSpatialTranslation_periodic (q : HillRealMeanZeroSource) :
    Function.Periodic (fun t => hillRealSpatialTranslation t q) 1 := by
  intro t
  change hillRealSpatialTranslation (t+1) q=hillRealSpatialTranslation t q
  rw [← hillRealSpatialTranslation_add t 1 q,hillRealSpatialTranslation_one]

/-- Covariance descends to the SAME actual physical real mean-zero field. -/
theorem hillRealActionHamiltonianVector_spatialTranslation (n : ℕ+) (t : ℝ) (q : HillRealMeanZeroSource) :
    hillRealActionHamiltonianVector n (hillRealSpatialTranslation t q)=
      hillRealSpatialTranslation t (hillRealActionHamiltonianVector n q) := by
  apply hillRealMeanZeroInclusion_injective
  rw [hillRealActionHamiltonianVector_inclusion,hillRealSpatialTranslation_inclusion,
    hillRealSpatialTranslation_inclusion,hillRealActionHamiltonianVector_inclusion]
  exact hillHminusActionHamiltonianVector_spatialTranslation n _ q.property t

end NLS.KdV
