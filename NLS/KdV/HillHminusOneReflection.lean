import NLS.KdV.HillHminusOneReality
import NLS.KdV.HillL2PrimitiveReflection

/-! # Exact Schwarz symmetry of the actual H^-1 Hill sheets

Real Fourier density transfers trace reflection from the physical L2
trace. The existing source-reflection theorem then fixes the precise
minus-conjugate sign of both the root and primitive, without a new
spectral sign or logarithm choice.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

/-- The actual entire H^-1 trace has physical Schwarz symmetry at every
real distributional potential, including nonzero mean. -/
theorem hillHminusDiscriminant_conj (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) :
    hillHminusDiscriminant q (conj z) = conj (hillHminusDiscriminant q z) := by
  have hc (w : ℂ) : Continuous (fun a : PeriodOneRealHminusOne => hillHminusDiscriminant a.val w) := by
    have hD : Continuous (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1) :=
      analyticOnNhd_hillHminusDiscriminant_joint.continuous
    have hm : Continuous (fun a : PeriodOneRealHminusOne => (w,a.val)) :=
      continuous_const.prodMk continuous_subtype_val
    exact Continuous.comp (g := fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1)
      (f := fun a : PeriodOneRealHminusOne => (w,a.val)) hD hm
  have he : (fun a : PeriodOneRealHminusOne => hillHminusDiscriminant a.val (conj z)) =
      (fun a : PeriodOneRealHminusOne => conj (hillHminusDiscriminant a.val z)) := by
    apply denseRange_periodOneRealL2Inclusion.equalizer (hc _) (hc z).star
    funext a
    change hillHminusDiscriminant (periodOneL2Inclusion a.val) (conj z) =
      conj (hillHminusDiscriminant (periodOneL2Inclusion a.val) z)
    rw [hillHminusDiscriminant_eq_hillL2,hillHminusDiscriminant_eq_hillL2]
    exact hillL2Discriminant_conj _ (IsRealHillPotential.periodDouble a.property) z
  exact congrFun he ⟨q,hq⟩

theorem hillHminusDiscriminant_real (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (x : ℝ) : (hillHminusDiscriminant q x).im = 0 := by
  have he := congrArg Complex.im (hillHminusDiscriminant_conj q hq (x : ℂ))
  simp only [conj_ofReal,conj_im] at he
  linarith

theorem hillHminusRadicand_conj (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) :
    hillHminusRadicand q (conj z) = conj (hillHminusRadicand q z) := by
  simp only [hillHminusRadicand,hillHminusDiscriminant_conj q hq,map_sub,map_pow,map_ofNat]

theorem hillHminusSourceFamily_schwarz (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : hillHminusSourceFamily.SourceSchwarzData q where
  domain_conj z hz := by
    rcases mem_slitPlane_iff.mp hz with hre | him
    · exact mem_slitPlane_iff.mpr (Or.inl (by simpa only [conj_re] using hre))
    · exact mem_slitPlane_iff.mpr (Or.inr (by simpa only [conj_im,neg_ne_zero] using him))
  free_conj z hz := classicalHillFreePrimitive_conj z hz
  trace_conj s z := hillHminusDiscriminant_conj _ (hq.smul_real s) z

theorem mem_hillHminusContinuationDomain_conj (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (ht : (z,q) ∈ hillHminusContinuationDomain) :
    (conj z,q) ∈ hillHminusContinuationDomain :=
  (hillHminusSourceFamily_schwarz q hq).continuation_conj z ht

theorem hillHminusContinuedRoot_conj (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (ht : (z,q) ∈ hillHminusContinuationDomain) :
    hillHminusContinuedRoot (conj z,q) = -conj (hillHminusContinuedRoot (z,q)) :=
  (hillHminusSourceFamily_schwarz q hq).root_conj z ht

theorem hillHminusContinuedPrimitive_conj (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (ht : (z,q) ∈ hillHminusContinuationDomain) :
    hillHminusContinuedPrimitive (conj z,q) = -conj (hillHminusContinuedPrimitive (z,q)) :=
  (hillHminusSourceFamily_schwarz q hq).primitive_conj z ht

theorem hillHminusContinuedPrimitive_re_eq_zero (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (x : ℝ) (ht : ((x : ℂ),q) ∈ hillHminusContinuationDomain) :
    (hillHminusContinuedPrimitive (x,q)).re = 0 := by
  have he := congrArg Complex.re (hillHminusContinuedPrimitive_conj q hq (x : ℂ) ht)
  simp only [conj_ofReal,neg_re,conj_re] at he
  linarith

/-- The actual normalized Floquet multiplier on the source domain. -/
def hillHminusContinuedMultiplier : ℂ × PeriodOneHminusOne → ℂ := hillHminusSourceFamily.multiplier

theorem exp_hillHminusContinuedPrimitive (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusContinuationDomain) :
    exp (hillHminusContinuedPrimitive t) = hillHminusContinuedMultiplier t :=
  hillHminusSourceFamily.exp_primitive t ht

theorem norm_hillHminusContinuedMultiplier_eq_one (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (x : ℝ) (ht : ((x : ℂ),q) ∈ hillHminusContinuationDomain) :
    ‖hillHminusContinuedMultiplier (x,q)‖ = 1 := by
  rw [← exp_hillHminusContinuedPrimitive _ ht,norm_exp,
    hillHminusContinuedPrimitive_re_eq_zero q hq x ht,Real.exp_zero]

end NLS.KdV
