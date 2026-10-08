import NLS.ComplexAnalysis.SineWeightedCubicIntegral
import NLS.ZakharovShabat.SourcePrimitivePowerRealBound
import NLS.ZakharovShabat.SourcePrimitivePowerAction

/-! # A quantitative cubic-moment lower bound from actual actions and gaps

The cleared inequality includes collapsed gaps. The quotient form uses Lean's
zero quotient at a collapsed gap, where the action and cubic moment both vanish.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- Cubic Jensen on the actual gap profile, with no lower-bound assumption on its height. -/
theorem real_action_cube_le_gap_sq_mul_cubic (φ : realTypeSourceSubmodule p) (n : ℤ) :
    Real.pi^2*‖sourceComplexAction hp hp1 n φ.val‖^3 ≤
      4*‖canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n‖^2*
        (A.moment n 3 φ.val).re := by
  let g := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
  let f := sourceRealGapCosineProfile hp hp1 φ.val n
  have hg : 0 ≤ g := by
    have h := realGapAffinePoint_cos_mem_Icc hp hp1 φ n 0
    simp only [g,canonicalPeriodicGap,sub_re]
    linarith [h.1,h.2]
  have hsq : ‖canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n‖^2 = g^2 := by
    have hr := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) n
    simp only [g,canonicalPeriodicGap,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,hr.1,hr.2,sub_self,mul_zero,add_zero]
    ring
  have hfirst : ‖sourceComplexAction hp hp1 n φ.val‖ =
      g/Real.pi*(∫ x in (0:ℝ)..Real.pi, Real.sin x*f x) := by
    rw [← A.moment_one n (A.realType_subset_domain φ.property),A.real_moment_norm_eq_re φ n 1]
    simpa only [Nat.mul_zero,Nat.zero_add,pow_one,ofReal_re] using
      congrArg Complex.re (A.real_odd_moment_eq_cosineIntegral φ n 0)
  have hthird : (A.moment n 3 φ.val).re =
      g/Real.pi*(∫ x in (0:ℝ)..Real.pi, Real.sin x*(f x)^3) := by
    exact congrArg Complex.re (A.real_odd_moment_eq_cosineIntegral φ n 1)
  have hj := NLS.ComplexAnalysis.sine_integral_cube_le f
    (sourceRealGapCosineProfile_continuous hp hp1 φ n)
    (fun x _ => sourceRealGapCosineProfile_nonneg hp hp1 φ n x)
  rw [hfirst,hthird,hsq]
  calc
    _ = (g^3/Real.pi)*(∫ x in (0:ℝ)..Real.pi, Real.sin x*f x)^3 := by
      field_simp
    _ ≤ (g^3/Real.pi)*(4*(∫ x in (0:ℝ)..Real.pi, Real.sin x*(f x)^3)) :=
      mul_le_mul_of_nonneg_left hj (div_nonneg (pow_nonneg hg _) Real.pi_pos.le)
    _ = _ := by ring

/-- A lower bound usable in sums, with a zero term at every collapsed gap. -/
theorem real_action_cube_div_gap_sq_le_cubic (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (Real.pi^2/4)*(‖sourceComplexAction hp hp1 n φ.val‖^3/
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n‖^2) ≤
        (A.moment n 3 φ.val).re := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · simp only [hg,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),div_zero,mul_zero]
    exact (A.real_moment_nonneg φ n 3).1
  have hpos : 0 < ‖canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hg)
  rw [← mul_div_assoc,div_le_iff₀ hpos]
  nlinarith [A.real_action_cube_le_gap_sq_mul_cubic φ n]

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
