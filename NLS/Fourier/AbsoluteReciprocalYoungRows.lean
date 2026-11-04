import NLS.Fourier.AbsoluteSampledRows
import NLS.SequenceSpaces.YoungConvolution

/-! # Absolute reciprocal rows at arbitrary Young exponents

The reciprocal kernel belongs to every exponent strictly above one.
An arbitrary Young relation therefore allows an arbitrarily small loss
from the input exponent, instead of fixing the doubled output exponent.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Fourier
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Positive Young convolution with the reciprocal kernel. -/
def absoluteReciprocalYoungMajorant (h : YoungRelation p q r) (hq1 : 1 < q) (a : Coeff p) : Coeff r :=
  Coeff.youngConvolution h (Coeff.magnitude a) (Coeff.magnitude (hilbertKernelCoeffs hq1))

omit [Fact (1 ≤ r)] in
/-- Each row converges absolutely at every admissible Young triple. -/
theorem summable_absoluteReciprocalYoungRow (h : YoungRelation p q r) (hq1 : 1 < q)
    (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k‖*‖hilbertKernel (n-k)‖) := by
  have hs := Coeff.summable_norm_youngConvolution_terms h a (hilbertKernelCoeffs hq1) n
  have ht := hs.comp_injective (Equiv.subLeft n).injective
  simpa only [Function.comp_def,Equiv.subLeft_apply,sub_sub_cancel,norm_mul,hilbertKernelCoeffs] using ht

/-- The coefficient norm is exactly the absolute reciprocal row. -/
theorem norm_absoluteReciprocalYoungMajorant_apply (h : YoungRelation p q r) (hq1 : 1 < q)
    (a : Coeff p) (n : ℤ) :
    ‖absoluteReciprocalYoungMajorant h hq1 a n‖ = ∑' k : ℤ, ‖a k‖*‖hilbertKernel (n-k)‖ := by
  rw [absoluteReciprocalYoungMajorant,Coeff.norm_magnitude_youngConvolution_apply]
  rw [← (Equiv.subLeft n).tsum_eq (fun k : ℤ => ‖a k‖*‖hilbertKernel (n-k)‖)]
  simp only [Equiv.subLeft_apply,sub_sub_cancel,hilbertKernelCoeffs]

/-- Young's constant is one; only the reciprocal-kernel norm remains. -/
theorem norm_absoluteReciprocalYoungMajorant_le (h : YoungRelation p q r) (hq1 : 1 < q)
    (a : Coeff p) :
    ‖absoluteReciprocalYoungMajorant h hq1 a‖ ≤ ‖a‖*‖hilbertKernelCoeffs hq1‖ :=
  Coeff.norm_magnitude_youngConvolution_le h a (hilbertKernelCoeffs hq1)

end NLS.Fourier
