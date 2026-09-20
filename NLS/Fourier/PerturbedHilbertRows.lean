import NLS.Fourier.HilbertSeries
import NLS.SequenceSpaces.ConvolutionMajorants
import NLS.ComplexAnalysis.ReciprocalPerturbation

/-!
# Off-diagonal reciprocal rows at perturbed integers

The sampling displacement may vary arbitrarily with the row. A uniform
half-unit bound gives a square-kernel majorant for the difference from the
ordinary Hilbert row, including at the totalized diagonal.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal is omitted before perturbing the sampled reciprocal denominator. -/
def perturbedHilbertTerm (t : ℤ → ℂ) (a : Coeff p) (n k : ℤ) : ℂ :=
  if k = n then 0 else a k/((k : ℂ)-n-t n)

/-- The positive square-kernel convolution majorizes the whole row correction. -/
def hilbertSquareMajorant (a : Coeff p) : Coeff p :=
  Coeff.convolution (Coeff.magnitude a) (Coeff.magnitude hilbertSquareCoeffs)

/-- The majorant's coefficient is exactly the absolute square-kernel row sum. -/
theorem norm_hilbertSquareMajorant_apply (a : Coeff p) (n : ℤ) :
    ‖hilbertSquareMajorant a n‖ = ∑' k : ℤ, ‖a k‖*‖hilbertSquareCoeffs (n-k)‖ := by
  rw [hilbertSquareMajorant, Coeff.norm_magnitude_convolution_apply]
  rw [← (Equiv.subLeft n).tsum_eq (fun k : ℤ => ‖a k‖*‖hilbertSquareCoeffs (n-k)‖)]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

/-- The square-kernel majorant has a uniform lp norm bound, also at p=1 and p=infinity. -/
theorem norm_hilbertSquareMajorant_le (a : Coeff p) :
    ‖hilbertSquareMajorant a‖ ≤ ‖a‖*‖hilbertSquareCoeffs‖ := by
  simpa only [hilbertSquareMajorant, Coeff.norm_magnitude] using
    Coeff.norm_convolution_le (Coeff.magnitude a) (Coeff.magnitude hilbertSquareCoeffs)

/-- Every square-kernel majorant row is absolutely summable. -/
theorem summable_hilbertSquareMajorant_row (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k‖*‖hilbertSquareCoeffs (n-k)‖) := by
  have h := Coeff.summable_norm_youngConvolution_terms
    (p := p) (q := 1) (r := p) (by simp [YoungRelation, add_comm]) a hilbertSquareCoeffs n
  have hh := h.comp_injective (Equiv.subLeft n).injective
  simpa only [Function.comp_def, Equiv.subLeft_apply, sub_sub_cancel, norm_mul] using hh

omit [Fact (1 ≤ p)] in
/-- Subtracting the unperturbed row gains a square reciprocal denominator. -/
theorem norm_perturbedHilbertTerm_sub_le (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2)
    (a : Coeff p) (n k : ℤ) :
    ‖perturbedHilbertTerm t a n k-a k/((k : ℂ)-n)‖ ≤ ‖a k‖*‖hilbertSquareCoeffs (n-k)‖ := by
  by_cases hkn : k = n
  · subst k
    simp [perturbedHilbertTerm, hilbertSquareCoeffs_apply]
  have ha : 1 ≤ ‖(k : ℂ)-n‖ := by
    rw [← Int.cast_sub, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkn)
  have h := NLS.ComplexAnalysis.norm_inv_sub_sub_inv_le ha (ht n)
  rw [perturbedHilbertTerm, if_neg hkn, div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, norm_mul]
  have he : ‖hilbertSquareCoeffs (n-k)‖ = ‖(k : ℂ)-n‖⁻¹^2 := by
    simp only [hilbertSquareCoeffs_apply, hilbertKernel, norm_pow, norm_neg, norm_inv, Int.cast_sub]
    rw [norm_sub_rev]
  rw [he]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- The correction terms are absolutely summable without a finite-p restriction. -/
theorem summable_norm_perturbedHilbert_correction (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2)
    (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖perturbedHilbertTerm t a n k-a k/((k : ℂ)-n)‖) :=
  (summable_hilbertSquareMajorant_row a n).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_perturbedHilbertTerm_sub_le t ht a n)

/-- The sum of correction terms is pointwise dominated by the positive lp majorant. -/
theorem norm_tsum_perturbedHilbert_correction_le (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2)
    (a : Coeff p) (n : ℤ) :
    ‖∑' k : ℤ, (perturbedHilbertTerm t a n k-a k/((k : ℂ)-n))‖ ≤ ‖hilbertSquareMajorant a n‖ := by
  rw [norm_hilbertSquareMajorant_apply]
  exact (norm_tsum_le_tsum_norm (summable_norm_perturbedHilbert_correction t ht a n)).trans
    ((summable_norm_perturbedHilbert_correction t ht a n).tsum_le_tsum
      (norm_perturbedHilbertTerm_sub_le t ht a n) (summable_hilbertSquareMajorant_row a n))

/-- The correction defines an lp coefficient sequence for every Banach exponent. -/
def perturbedHilbertCorrection (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) : Coeff p :=
  ⟨fun n => ∑' k : ℤ, (perturbedHilbertTerm t a n k-a k/((k : ℂ)-n)),
    (lp.memℓp (hilbertSquareMajorant a)).mono' (norm_tsum_perturbedHilbert_correction_le t ht a)⟩

/-- The lp norm of the row correction is uniform over all admissible sampling sequences. -/
theorem norm_perturbedHilbertCorrection_le (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) :
    ‖perturbedHilbertCorrection t ht a‖ ≤ ‖a‖*‖hilbertSquareCoeffs‖ :=
  (lp.norm_mono (x := perturbedHilbertCorrection t ht a) (y := hilbertSquareMajorant a)
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (norm_tsum_perturbedHilbert_correction_le t ht a)).trans (norm_hilbertSquareMajorant_le a)

end NLS.Fourier
