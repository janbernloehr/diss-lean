import NLS.SequenceSpaces.YoungConvolution

/-! Young convolution intertwines translations and the genuine Wiener
convolution module action. All exponents and the infinity output are retained. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Translation of the second input translates the output, with the actual sums. -/
theorem youngConvolution_shift_right (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (k : ℤ) :
    youngConvolution h a (shift k b) = shift k (youngConvolution h a b) := by
  ext n
  rw [youngConvolution_apply, shift_apply, youngConvolution_apply]
  rw [← (Equiv.addRight k).tsum_eq (fun j : ℤ => a (n-j)*shift k b j)]
  apply tsum_congr
  intro j
  change a (n-(j+k))*b (j+k-k) = a (n-k-j)*b j
  rw [show n-(j+k) = n-k-j by omega, add_sub_cancel_right]

/-- Associativity with a Wiener right factor is an identity of actual
Banach-space convolutions, including the L2,L2-to-infinity case. -/
theorem youngConvolution_convolution_right (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (c : Coeff 1) :
    youngConvolution h a (convolution b c) = convolution (youngConvolution h a b) c := by
  change youngConvolutionCLM h a (∑' k : ℤ, c k • shift k b) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_convolution_terms b c)]
  unfold convolution
  apply tsum_congr
  intro k
  rw [map_smul, youngConvolutionCLM_apply, youngConvolution_shift_right]

end NLS.Coeff
