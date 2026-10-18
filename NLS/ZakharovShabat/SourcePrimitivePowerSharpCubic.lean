import NLS.ComplexAnalysis.SineIntegralKernelCorrection
import NLS.ZakharovShabat.SourcePrimitivePowerRealBound
import NLS.ZakharovShabat.SourcePrimitivePowerAction

/-! # A sharp cubic moment bound conditional on the actual gap profile

The exact real action and cubic-moment integrals convert the scalar profile
ratio into R_n >= (3/4)*|I_n|^2. A positive exterior-kernel representation
with an integrable majorant supplies the required scalar hypotheses.
The representation of the actual discriminant profile is an explicit
hypothesis: this module does not construct it.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- A normalized correction profile with a positive linear moment gives the sharp actual cubic bound.
The representation remains an explicit hypothesis; it is not supplied by this theorem. -/
theorem real_action_sq_le_cubic_of_profile_correction
    (φ : realTypeSourceSubmodule p) (n : ℤ) (V : ℝ → ℝ)
    (hV : Continuous V) (hn : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, 0 ≤ V x)
    (hlinear : 0 ≤ ∫ x in (0:ℝ)..Real.pi,
      (2*(Real.sin x)^4-(Real.sin x)^2)*V x)
    (hrep : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
      sourceRealGapCosineProfile hp hp1 φ.val n x =
        (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/2*
          Real.sin x*(1+V x)) :
    (3/4:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖^2 ≤ (A.moment n 3 φ.val).re := by
  let g := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
  let f := sourceRealGapCosineProfile hp hp1 φ.val n
  change ∀ x ∈ Set.Icc (0:ℝ) Real.pi, f x = g/2*Real.sin x*(1+V x) at hrep
  have hfirst : ‖sourceComplexAction hp hp1 n φ.val‖ =
      g/Real.pi*(∫ x in (0:ℝ)..Real.pi, Real.sin x*f x) := by
    rw [← A.moment_one n (A.realType_subset_domain φ.property),A.real_moment_norm_eq_re φ n 1]
    simpa only [Nat.mul_zero,Nat.zero_add,pow_one,Complex.ofReal_re] using
      congrArg Complex.re (A.real_odd_moment_eq_cosineIntegral φ n 0)
  have hthird : (A.moment n 3 φ.val).re =
      g/Real.pi*(∫ x in (0:ℝ)..Real.pi, Real.sin x*(f x)^3) :=
    congrArg Complex.re (A.real_odd_moment_eq_cosineIntegral φ n 1)
  have ha : (∫ x in (0:ℝ)..Real.pi, Real.sin x*f x) =
      (g/2)*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le Real.pi_pos.le] at hx
    dsimp only
    rw [hrep x hx]
    ring
  have hb : (∫ x in (0:ℝ)..Real.pi, Real.sin x*(f x)^3) =
      (g/2)^3*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(1+V x)^3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le Real.pi_pos.le] at hx
    dsimp only
    rw [hrep x hx]
    ring
  have h := NLS.ComplexAnalysis.scaled_profile_cubic_lower_bound (g/2) _ _
    (NLS.ComplexAnalysis.sine_corrected_profile_cubic V hV hn hlinear)
  rw [hfirst,hthird,ha,hb]
  convert! h using 1 <;> ring

/-- A positive exterior-kernel representation supplies the sharp actual cubic estimate. -/
theorem real_action_sq_le_cubic_of_exterior_kernel_representation
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.SFinite μ]
    (c s : α → ℝ) (hcm : Measurable c) (hsm : Measurable s)
    (hc : ∀ a, 0 ≤ c a) (hs : ∀ a, 1 < |s a|)
    (hint : MeasureTheory.Integrable (fun a => c a/(|s a|-1)) μ)
    (hrep : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
      sourceRealGapCosineProfile hp hp1 φ.val n x =
        (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/2*
          Real.sin x*(1+(∫ a, c a/|s a-Real.cos x| ∂μ))) :
    (3/4:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖^2 ≤ (A.moment n 3 φ.val).re := by
  apply A.real_action_sq_le_cubic_of_profile_correction φ n _
    (NLS.ComplexAnalysis.continuous_integral_exterior_cosine_kernel μ c s hcm hsm hc hs hint)
  · intro x _
    exact MeasureTheory.integral_nonneg (fun a => div_nonneg (hc a) (abs_nonneg _))
  · exact NLS.ComplexAnalysis.sine_integral_kernel_correction_nonneg μ c s
      (Filter.Eventually.of_forall hc) (Filter.Eventually.of_forall hs)
      (NLS.ComplexAnalysis.integrable_sine_exterior_kernel_correction μ c s hcm hsm hc hs hint)
  · exact hrep

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
