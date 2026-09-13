import NLS.SequenceSpaces.IteratedConvolutionRows

/-!
# Absolutely convergent double sums for iterated rows

The nested row norm is the precise two-index power sum. Joint summability
justifies changing the order of the two reciprocal indices.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- The outer coefficient's power is exactly its inner power sum. -/
theorem iteratedConvolutionRow_norm_apply_rpow (hr : 0 < r.toReal)
    (a : Coeff p) (b c : Coeff r) (m j : ℤ) :
    ‖iteratedConvolutionRow a b c m j‖^r.toReal =
      ∑' k : ℤ, ‖a (m-j-k) * c k * b j‖^r.toReal := by
  rw [iteratedConvolutionRow_apply, norm_mul, Complex.norm_real, norm_norm,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _), lp.norm_rpow_eq_tsum hr, ← tsum_mul_right]
  apply tsum_congr
  intro k
  simp only [convolutionRow_apply, norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)]

omit [Fact (1 ≤ r)] in
/-- The inner sum is absolutely convergent at every pair of outer indices. -/
theorem summable_iteratedConvolutionRow_inner (hr : 0 < r.toReal)
    (a : Coeff p) (b c : Coeff r) (m j : ℤ) :
    Summable (fun k : ℤ => ‖a (m-j-k) * c k * b j‖^r.toReal) := by
  have h := ((lp.memℓp (convolutionRow a c (m-j))).summable hr).mul_right (‖b j‖^r.toReal)
  simpa only [convolutionRow_apply, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)] using h

/-- The double power series is jointly summable, not just iteratively summable. -/
theorem summable_iteratedConvolutionRow_prod (hr : 0 < r.toReal)
    (a : Coeff p) (b c : Coeff r) (m : ℤ) :
    Summable (fun jk : ℤ × ℤ => ‖a (m-jk.1-jk.2) * c jk.2 * b jk.1‖^r.toReal) := by
  apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
  refine ⟨summable_iteratedConvolutionRow_inner hr a b c m, ?_⟩
  simpa only [← iteratedConvolutionRow_norm_apply_rpow hr] using
    (lp.memℓp (iteratedConvolutionRow a b c m)).summable hr

/-- Exact two-index power formula for the iterated row norm. -/
theorem norm_iteratedConvolutionRow_rpow (hr : 0 < r.toReal)
    (a : Coeff p) (b c : Coeff r) (m : ℤ) :
    ‖iteratedConvolutionRow a b c m‖^r.toReal =
      ∑' j : ℤ, ∑' k : ℤ, ‖a (m-j-k) * c k * b j‖^r.toReal := by
  rw [lp.norm_rpow_eq_tsum hr]
  exact tsum_congr (iteratedConvolutionRow_norm_apply_rpow hr a b c m)

/-- Interchanging the two kernels preserves the exact nested row norm. -/
theorem norm_iteratedConvolutionRow_swap (hr : 0 < r.toReal)
    (a : Coeff p) (b c : Coeff r) (m : ℤ) :
    ‖iteratedConvolutionRow a b c m‖ = ‖iteratedConvolutionRow a c b m‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hr.ne').mp
  calc
    _ = ∑' j : ℤ, ∑' k : ℤ, ‖a (m-j-k) * c k * b j‖^r.toReal :=
      norm_iteratedConvolutionRow_rpow hr a b c m
    _ = ∑' k : ℤ, ∑' j : ℤ, ‖a (m-j-k) * c k * b j‖^r.toReal :=
      (Summable.tsum_comm (f := fun j k : ℤ => ‖a (m-j-k) * c k * b j‖^r.toReal)
        (summable_iteratedConvolutionRow_prod hr a b c m)).symm
    _ = ∑' k : ℤ, ∑' j : ℤ, ‖a (m-k-j) * b j * c k‖^r.toReal := by
      apply tsum_congr
      intro k
      apply tsum_congr
      intro j
      rw [show m-j-k = m-k-j by omega, mul_right_comm]
    _ = _ := (norm_iteratedConvolutionRow_rpow hr a c b m).symm

end NLS.Coeff
