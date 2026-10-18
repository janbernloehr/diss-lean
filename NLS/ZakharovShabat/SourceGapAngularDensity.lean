import NLS.ZakharovShabat.SourcePrimitivePowerCubicLowerBound
import NLS.ZakharovShabat.SourceWeightedActionMajorant
import Mathlib.MeasureTheory.Integral.Prod

/-! # Positive angular densities of the actual spectral gaps

Each angular density integrates to one half of its original action.
Summable actions therefore give joint integrability over the exterior
gap indices and angles. Real Hilbert inputs supply this summability.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Positive angular density whose integral is one half of the actual indexed action. -/
def sourceGapAngularDensity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (θ : ℝ) : ℝ :=
  (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re /
    (2*Real.pi) * (Icc (0:ℝ) Real.pi).indicator
      (fun x => Real.sin x*sourceRealGapCosineProfile hp hp1 φ.val n x) θ

theorem sourceGapAngularDensity_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (θ : ℝ) :
    0 ≤ sourceGapAngularDensity hp hp1 φ n θ := by
  have hg : 0 ≤ (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re := by
    have h := NLS.ComplexAnalysis.re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)).2.1 n)
    simpa only [canonicalPeriodicGap,Complex.sub_re,sub_nonneg] using h
  apply mul_nonneg (div_nonneg hg (by positivity))
  by_cases hθ : θ ∈ Icc (0:ℝ) Real.pi
  · rw [indicator_of_mem hθ]
    exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ)
  · rw [indicator_of_notMem hθ]

theorem measurable_sourceGapAngularDensity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : Measurable (sourceGapAngularDensity hp hp1 φ n) := by
  unfold sourceGapAngularDensity
  exact ((Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous hp hp1 φ n)).measurable.indicator
    measurableSet_Icc).const_mul _

theorem integrable_sourceGapAngularDensity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : Integrable (sourceGapAngularDensity hp hp1 φ n) := by
  unfold sourceGapAngularDensity
  exact ((Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous hp hp1 φ n)).continuousOn.integrableOn_Icc.integrable_indicator
    measurableSet_Icc).const_mul _

/-- The original action normalization is retained exactly in angular coordinates. -/
theorem integral_sourceGapAngularDensity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (∫ θ : ℝ, sourceGapAngularDensity hp hp1 φ n θ) =
      (1/2:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖ := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  have hfirst : ‖sourceComplexAction hp hp1 n φ.val‖ =
      (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/Real.pi*
        (∫ x in (0:ℝ)..Real.pi, Real.sin x*sourceRealGapCosineProfile hp hp1 φ.val n x) := by
    rw [← A.moment_one n (A.realType_subset_domain φ.property),A.real_moment_norm_eq_re φ n 1]
    simpa only [Nat.mul_zero,Nat.zero_add,pow_one,Complex.ofReal_re] using
      congrArg Complex.re (A.real_odd_moment_eq_cosineIntegral φ n 0)
  unfold sourceGapAngularDensity
  rw [integral_const_mul,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le,hfirst]
  ring

theorem integral_norm_sourceGapAngularDensity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (∫ θ : ℝ, ‖sourceGapAngularDensity hp hp1 φ n θ‖) =
      (1/2:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖ := by
  simp_rw [Real.norm_eq_abs,abs_of_nonneg (sourceGapAngularDensity_nonneg hp hp1 φ n _)]
  exact integral_sourceGapAngularDensity hp hp1 φ n

/-- The actual Hilbert action trace controls the whole family of angular densities in L1. -/
theorem summable_integral_norm_sourceGapAngularDensity (φ : realTypeSourceSubmodule 2) :
    Summable (fun n : ℤ => ∫ θ : ℝ, ‖sourceGapAngularDensity (by simp) (by norm_num) φ n θ‖) := by
  simpa only [integral_norm_sourceGapAngularDensity,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) _ φ.val φ.property,
    norm_sourceRealAction] using (sourceRealActions_summable φ).mul_left (1/2:ℝ)

/-- Summable actions make the exterior densities jointly integrable at any exponent. -/
theorem integrable_sourceGapAngularDensity_exterior_of_summable (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (ha : Summable (fun m : ℤ => ‖sourceComplexAction hp hp1 m φ.val‖)) :
    Integrable (fun z : {m : ℤ // m ≠ n} × ℝ => sourceGapAngularDensity hp hp1 φ z.1.val z.2)
      (Measure.count.prod volume) := by
  have hm : Measurable (fun z : {m : ℤ // m ≠ n} × ℝ => sourceGapAngularDensity hp hp1 φ z.1.val z.2) :=
    measurable_from_prod_countable_right (fun m => measurable_sourceGapAngularDensity hp hp1 φ m.val)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun m => integrable_sourceGapAngularDensity hp hp1 φ m.val),?_⟩
  apply integrable_count_iff.mpr
  have hs : Summable (fun m : ℤ => ∫ θ : ℝ, ‖sourceGapAngularDensity hp hp1 φ m θ‖) := by
    simpa only [integral_norm_sourceGapAngularDensity] using ha.mul_left (1/2:ℝ)
  have he (m : {m : ℤ // m ≠ n}) :
      ‖∫ θ : ℝ, ‖sourceGapAngularDensity hp hp1 φ m.val θ‖‖ =
        ∫ θ : ℝ, ‖sourceGapAngularDensity hp hp1 φ m.val θ‖ :=
    Real.norm_of_nonneg (integral_nonneg (fun θ : ℝ => norm_nonneg (sourceGapAngularDensity hp hp1 φ m.val θ)))
  simp_rw [he]
  exact hs.subtype (fun m => m ≠ n)

/-- No summability premise is needed for a real Hilbert input. -/
theorem integrable_sourceGapAngularDensity_exterior (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    Integrable (fun z : {m : ℤ // m ≠ n} × ℝ =>
      sourceGapAngularDensity (by simp) (by norm_num) φ z.1.val z.2)
      (Measure.count.prod volume) := by
  apply integrable_sourceGapAngularDensity_exterior_of_summable
  simpa only [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) _ φ.val φ.property,
    norm_sourceRealAction] using sourceRealActions_summable φ

end NLS.ZakharovShabat
