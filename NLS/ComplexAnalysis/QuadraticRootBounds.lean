import NLS.ComplexAnalysis.QuadraticRootPrimitive

/-!
# Bounds independent of the sign of a quadratic root

The square identity controls a terminal root by its displacement from
the midpoint and half the gap. Lower bounds on both endpoint distances
control either choice of square root on an enclosing contour.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- This estimate also applies to a zero gap or a zero terminal root. -/
theorem norm_le_of_sq_eq_gap_polynomial (B z γ : ℂ)
    (hsq : B^2 = z^2-γ^2/4) : ‖B‖ ≤ ‖z‖+‖γ‖/2 := by
  have h := norm_sub_le (z^2) (γ^2/4)
  rw [← hsq,norm_pow,norm_pow,norm_div,norm_pow] at h
  have hfour : ‖(4:ℂ)‖ = (4:ℝ) := by norm_num
  rw [hfour] at h
  nlinarith [norm_nonneg B,norm_nonneg z,norm_nonneg γ]

/-- Endpoint separation bounds either sheet of the selected root. -/
theorem norm_ge_of_sq_eq_endpoint_product (Q a b z : ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hsq : Q^2 = (a-z)*(b-z))
    (ha : δ ≤ ‖a-z‖) (hb : δ ≤ ‖b-z‖) : δ ≤ ‖Q‖ := by
  have h := mul_le_mul ha hb hδ (norm_nonneg _)
  have hn := congrArg norm hsq
  rw [norm_pow,norm_mul] at hn
  nlinarith [norm_nonneg Q]

end NLS.ComplexAnalysis
