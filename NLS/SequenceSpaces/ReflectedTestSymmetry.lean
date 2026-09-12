import NLS.SequenceSpaces.TestConvolution

/-!
# Symmetry of reflected bilinear convolution tests

The scalar potential need only be in `ℓᵖ`; both test factors are in `ℓ¹`.
This gives the transpose identity used in the bilinear Green formula without
requiring Hilbert-space adjoints or restricting the exponent to two.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original Banach convolution is commutative when both factors are in `ℓ¹`. -/
theorem convolution_comm_one (b c : Coeff 1) : convolution b c = convolution c b := by
  ext n
  rw [convolution_apply, convolution_apply,
    ← (Equiv.subLeft n).tsum_eq (fun k : ℤ => c (n-k) * b k)]
  apply tsum_congr
  intro k
  simp only [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]

/-- Testing a potential product against a reflected test is symmetric in the two tests. -/
theorem testPairing_convolution_reflection_symm (a : Coeff p) (b c : Coeff 1) :
    testPairing (convolution a b) (reflection c) = testPairing (convolution a c) (reflection b) := by
  rw [testPairing_convolution, testPairing_convolution, convolution_comm_one]

/-- Reflection makes the unconjugated Fourier product symmetric. -/
theorem tsum_reflected_product_symm (a b : ℤ → ℂ) :
    (∑' k : ℤ, a k * b (-k)) = ∑' k : ℤ, b k * a (-k) := by
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => b k * a (-k))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, neg_neg, mul_comm]

/-- Reflection reverses the sign of the linear free symbol in a bilinear test. -/
theorem tsum_reflected_linear_symm (a b : ℤ → ℂ) (z t : ℂ) :
    (∑' k : ℤ, (z + t * k) * a k * b (-k)) = ∑' k : ℤ, (z - t * k) * b k * a (-k) := by
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => (z - t * k) * b k * a (-k))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, neg_neg, Int.cast_neg]
  ring

end NLS.Coeff
