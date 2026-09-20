import NLS.Fourier.SampledHilbert
import NLS.SequenceSpaces.ProductRowExponents

/-!
# Doubled-exponent bounds for absolute sampled rows

Young's inequality puts the absolute reciprocal row in l^(2p), with kernel
exponent (2p)'. The majorant depends only on the input, not on the complex
sampling displacements, so it is uniform over every half-unit sampling family.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩
local instance : Fact (1 ≤ (2*p).conjExponent) := ⟨ENNReal.HolderConjugate.one_le (2*p).conjExponent (2*p)⟩

/-- A fixed reciprocal-kernel constant for the doubled-exponent row estimate. -/
def absoluteSampledRowConstant (hp : p ≠ ⊤) : ℝ :=
  2*‖hilbertKernelCoeffs (one_lt_double_conjugate hp)‖

/-- The reciprocal-row constant is nonnegative. -/
theorem absoluteSampledRowConstant_nonneg (hp : p ≠ ⊤) : 0 ≤ absoluteSampledRowConstant hp := by
  unfold absoluteSampledRowConstant
  positivity

/-- The positive convolution majorant for all admissible sampling sequences. -/
def absoluteSampledRowMajorant (hp : p ≠ ⊤) (a : Coeff p) : Coeff (2*p) :=
  (2 : ℂ) • Coeff.youngConvolution (youngRelation_double_conjugate p)
    (Coeff.magnitude a) (Coeff.magnitude (hilbertKernelCoeffs (one_lt_double_conjugate hp)))

/-- The majorant norm is bounded linearly by the input norm. -/
theorem norm_absoluteSampledRowMajorant_le (hp : p ≠ ⊤) (a : Coeff p) :
    ‖absoluteSampledRowMajorant hp a‖ ≤ absoluteSampledRowConstant hp*‖a‖ := by
  rw [absoluteSampledRowMajorant, norm_smul]
  norm_num only [Complex.norm_ofNat]
  have h := mul_le_mul_of_nonneg_left (Coeff.norm_magnitude_youngConvolution_le
    (youngRelation_double_conjugate p) a (hilbertKernelCoeffs (one_lt_double_conjugate hp))) (by norm_num : (0 : ℝ) ≤ 2)
  exact h.trans_eq (by unfold absoluteSampledRowConstant; ring)

/-- The majorant coefficient is twice the absolute reciprocal row. -/
theorem norm_absoluteSampledRowMajorant_apply (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    ‖absoluteSampledRowMajorant hp a n‖ = 2*∑' k : ℤ, ‖a k‖*‖hilbertKernel (n-k)‖ := by
  change ‖(2 : ℂ)*Coeff.youngConvolution _ _ _ n‖ = _
  rw [norm_mul, Coeff.norm_magnitude_youngConvolution_apply]
  norm_num only [Complex.norm_ofNat]
  rw [← (Equiv.subLeft n).tsum_eq (fun k : ℤ => ‖a k‖*‖hilbertKernel (n-k)‖)]
  simp only [Equiv.subLeft_apply, sub_sub_cancel, hilbertKernelCoeffs]

/-- Each absolute reciprocal row is summable for every finite Banach input exponent. -/
theorem summable_absoluteSampledRow (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k‖*‖hilbertKernel (n-k)‖) := by
  have h := Coeff.summable_norm_youngConvolution_terms (youngRelation_double_conjugate p)
    a (hilbertKernelCoeffs (one_lt_double_conjugate hp)) n
  have hh := h.comp_injective (Equiv.subLeft n).injective
  simpa only [Function.comp_def, Equiv.subLeft_apply, sub_sub_cancel, norm_mul, hilbertKernelCoeffs] using hh

omit [Fact (1 ≤ p)] in
/-- Every perturbed term is bounded by twice its unperturbed absolute reciprocal kernel. -/
theorem norm_perturbedHilbertTerm_le (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2)
    (a : Coeff p) (n k : ℤ) :
    ‖perturbedHilbertTerm t a n k‖ ≤ 2*(‖a k‖*‖hilbertKernel (n-k)‖) := by
  by_cases hkn : k = n
  · subst k
    simp [perturbedHilbertTerm, hilbertKernel]
  have ha : 1 ≤ ‖(k : ℂ)-n‖ := by
    rw [← Int.cast_sub, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkn)
  have h := mul_le_mul_of_nonneg_left (NLS.ComplexAnalysis.norm_inv_sub_le ha (ht n)) (norm_nonneg (a k))
  rw [perturbedHilbertTerm, if_neg hkn, div_eq_mul_inv, norm_mul]
  have he : ‖hilbertKernel (n-k)‖ = ‖(k : ℂ)-n‖⁻¹ := by
    simp only [hilbertKernel, norm_neg, norm_inv, Int.cast_sub]
    rw [norm_sub_rev]
  rw [he]
  exact h.trans_eq (by ring)

/-- The doubled-exponent majorant bounds the absolute sum uniformly in the samples. -/
theorem tsum_norm_perturbedHilbert_le_majorant (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) (n : ℤ) :
    (∑' k : ℤ, ‖perturbedHilbertTerm t a n k‖) ≤ ‖absoluteSampledRowMajorant hp a n‖ := by
  have hs := (summable_absoluteSampledRow hp a n).mul_left 2
  have hu := hs.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_perturbedHilbertTerm_le t ht a n)
  rw [norm_absoluteSampledRowMajorant_apply, ← tsum_mul_left]
  exact hu.tsum_le_tsum (norm_perturbedHilbertTerm_le t ht a n) hs

end NLS.Fourier
