import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity
import NLS.ZakharovShabat.UniformCanonicalCriticalPoints
import NLS.ZakharovShabat.SourceLemma8_2
import NLS.ZakharovShabat.RealDiscriminantExtrema
import NLS.ZakharovShabat.SourceCriticalPointsAnalytic

/-!
# Lemma 8.5 and the real critical-point interlacing statements

The actual canonical critical roots are ordered, retain their analytic
multiplicities, and have locally bounded ℓp displacements in the original
source space. Their literal symmetric products give the discriminant
derivative on the entire spectral plane, with prefactor two and the
exceptional denominator one at index zero.

At real type, complex source perturbations preserve coordinate continuity
and full sequence-norm continuity. Every real gap has exactly one critical
point and one strict real local extremum, including collapsed gaps.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual ordered critical sequence, its ℓp displacement, and literal derivative product. -/
structure SourceLemma8_5Data (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : Prop where
  ordered : Monotone (fun n => complexLexKey (canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n))
  roots : ∀ z : ℂ, deriv (canonicalDiscriminant hp (periodOnePotential φ)) z = 0 ↔
    ∃ n : ℤ, canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = z
  multiplicity : ∀ z : ℂ,
    (∑ᶠ n : ℤ, if canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = z then (1 : ℕ) else 0) =
      analyticOrderNatAt (deriv (canonicalDiscriminant hp (periodOnePotential φ))) z
  displacement : ∀ n : ℤ,
    canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n =
      (Real.pi : ℂ)*n+sourceCriticalDisplacement hp hp1 φ n
  product : TendstoLocallyUniformlyOn
    (fun (M : ℕ) (z : ℂ) => 2 * ∏ n ∈ Finset.Icc (-(M : ℤ)) M,
      (canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n-z)/
        (if n = 0 then 1 else (Real.pi : ℂ)*n))
    (deriv (canonicalDiscriminant hp (periodOnePotential φ))) atTop univ

/-- The pointwise part of Lemma 8.5, including exact analytic multiplicities. -/
theorem sourceLemma8_5_data (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    SourceLemma8_5Data hp hp1 φ where
  ordered := monotone_canonicalCriticalPoints hp hp1 _ (periodOnePotential_mem φ)
  roots := canonicalCriticalPoints_exhaustive hp hp1 _ (periodOnePotential_mem φ)
  multiplicity := canonicalCriticalPoints_multiplicity hp hp1 _ (periodOnePotential_mem φ)
  displacement := by
    intro n
    simp only [sourceCriticalDisplacement,canonicalCriticalDisplacement_apply]
    ring
  product := by
    simpa only [singleSpectralPartialProduct,singleSpectralFactor,singleSpectralDenominator] using
      tendstoLocallyUniformlyOn_canonicalCriticalProduct hp hp1 _ (periodOnePotential_mem φ)

/-- Lemma 8.5 with a common original neighborhood and full ℓp displacement bound. -/
theorem sourceLemma8_5 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U,
        ‖sourceCriticalDisplacement hp hp1 ψ‖ ≤ R ∧ SourceLemma8_5Data hp hp1 ψ := by
  obtain ⟨_,_,U,ho,hc,hφ,h0,R,hR,hb⟩ := exists_uniform_canonicalCriticalPoints hp hp1 (periodOnePotential φ)
  refine ⟨periodOnePotential ⁻¹' U,ho.preimage (periodOnePotential (p := p)).continuous,
    hc.linear_preimage ((periodOnePotential (p := p)).restrictScalars ℝ).toLinearMap,
    hφ,by simpa only [mem_preimage,map_zero] using h0,R,hR,?_⟩
  intro ψ hψ
  exact ⟨(hb _ hψ (periodOnePotential_mem ψ)).2,sourceLemma8_5_data hp hp1 ψ⟩

/-- Real-type continuity and the following interlacing and strict-extremum assertions. -/
structure SourceLemma8_5RealData (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : Prop where
  continuous : ∀ n : ℤ, ContinuousAt (fun ψ : CoeffPair p =>
    canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
  analytic : ∀ n : ℤ, AnalyticAt ℂ (fun ψ : CoeffPair p =>
    canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
  norm_continuity : ContinuousAt (sourceCriticalDisplacement hp hp1) φ
  real_coordinates : ∀ n : ℤ,
    (canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).im = 0
  interlacing : ∀ n : ℤ,
    (canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re ∈ sourceRealPeriodicGap hp hp1 φ n
  unique_critical : ∀ n : ℤ, ∃! z : ℂ,
    deriv (canonicalDiscriminant hp (periodOnePotential φ)) z = 0 ∧ z.re ∈ sourceRealPeriodicGap hp hp1 φ n
  strict_extremum : ∀ n : ℤ,
    let c := (canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    (∀ᶠ y : ℝ in 𝓝[≠] c, (canonicalDiscriminant hp (periodOnePotential φ) c).re < (canonicalDiscriminant hp (periodOnePotential φ) y).re) ∨
    (∀ᶠ y : ℝ in 𝓝[≠] c, (canonicalDiscriminant hp (periodOnePotential φ) y).re < (canonicalDiscriminant hp (periodOnePotential φ) c).re)
  unique_extremum : ∀ n : ℤ, ∃! x : ℝ,
    IsLocalExtr (fun y : ℝ => (canonicalDiscriminant hp (periodOnePotential φ) y).re) x ∧ x ∈ sourceRealPeriodicGap hp hp1 φ n
  all_extrema : ∀ x : ℝ,
    IsLocalExtr (fun y : ℝ => (canonicalDiscriminant hp (periodOnePotential φ) y).re) x ↔
      ∃ n : ℤ, canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = (x : ℂ)

/-- The real-type conclusions, with arbitrary complex source perturbations in continuity. -/
theorem sourceLemma8_5_real (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) : SourceLemma8_5RealData hp hp1 φ where
  continuous := fun n => (analyticAt_sourceCanonicalCriticalPoint_of_realType hp hp1 n φ hφ).continuousAt
  analytic := fun n => analyticAt_sourceCanonicalCriticalPoint_of_realType hp hp1 n φ hφ
  norm_continuity := continuousAt_sourceCriticalDisplacement_of_realType hp hp1 φ hφ
  real_coordinates := canonicalCriticalPoints_im_eq_zero hp hp1 _ (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ)
  interlacing := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 _ (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ)
  unique_critical := existsUnique_critical_in_canonicalPeriodicGap hp hp1 _ (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ)
  strict_extremum := canonicalCriticalPoints_strict_local_extremum hp hp1 _ (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ)
  unique_extremum := existsUnique_localExtremum_in_canonicalPeriodicGap hp hp1 _ (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ)
  all_extrema := isLocalExtr_real_discriminant_iff_canonical hp hp1 _ (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ)

/-- One source neighborhood controls every critical coordinate at the same time. -/
theorem SourceLemma8_5RealData.exists_uniform_coordinate_neighborhood
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p} (D : SourceLemma8_5RealData hp hp1 φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∀ ψ ∈ V, ∀ n : ℤ,
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ < ε := by
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp D.norm_continuity ε hε
  refine ⟨Metric.ball φ δ,Metric.isOpen_ball,Metric.mem_ball_self hδ,?_⟩
  intro ψ hψ n
  have hb : ‖sourceCriticalDisplacement hp hp1 ψ-sourceCriticalDisplacement hp hp1 φ‖ < ε := by
    simpa only [dist_eq_norm] using hd hψ
  have h := (lp.norm_apply_le_norm ((zero_lt_one.trans hp1).ne')
    (sourceCriticalDisplacement hp hp1 ψ-sourceCriticalDisplacement hp hp1 φ) n).trans_lt hb
  simpa only [sourceCriticalDisplacement,lp.coeFn_sub,Pi.sub_apply,
    canonicalCriticalDisplacement_apply,sub_sub_sub_cancel_right] using h

end NLS.ZakharovShabat
