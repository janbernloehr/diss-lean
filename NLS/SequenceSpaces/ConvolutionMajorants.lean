import NLS.SequenceSpaces.SandwichMajorant
import NLS.SequenceSpaces.YoungInequality

/-!
# Positive majorants for single convolution rows

The convolution of coefficient magnitudes realizes the scalar absolute row
sum exactly and preserves the existing sharp Young norm bound.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- The magnitude convolution has norm equal to the absolute scalar row sum. -/
theorem norm_magnitude_youngConvolution_apply (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (n : ℤ) :
    ‖youngConvolution h (magnitude a) (magnitude b) n‖ = ∑' k : ℤ, ‖a (n-k)‖*‖b k‖ := by
  change ‖∑' k : ℤ, magnitude a (n-k)*magnitude b k‖ = _
  simp only [magnitude_apply, ← Complex.ofReal_mul, ← Complex.ofReal_tsum, Complex.norm_real]
  exact Real.norm_of_nonneg (tsum_nonneg (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)))

/-- Positive majorants obey the same constant-one Young inequality. -/
theorem norm_magnitude_youngConvolution_le (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    ‖youngConvolution h (magnitude a) (magnitude b)‖ ≤ ‖a‖*‖b‖ := by
  simpa only [norm_magnitude] using norm_youngConvolution_le h (magnitude a) (magnitude b)

/-- With an lp input and summable kernel the absolute row is the norm of an lp coefficient. -/
theorem norm_magnitude_convolution_apply (a : Coeff p) (b : Coeff 1) (n : ℤ) :
    ‖convolution (magnitude a) (magnitude b) n‖ = ∑' k : ℤ, ‖a (n-k)‖*‖b k‖ := by
  rw [convolution_apply]
  simp only [magnitude_apply, ← Complex.ofReal_mul, ← Complex.ofReal_tsum, Complex.norm_real]
  exact Real.norm_of_nonneg (tsum_nonneg (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)))

end NLS.Coeff
