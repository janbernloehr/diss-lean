import NLS.SequenceSpaces.ConvolutionSandwich

/-!
# Positive coefficient majorants for convolution sandwiches

Replacing coefficients by their magnitudes preserves their sequence norms.
The resulting sandwich has nonnegative real coefficients and realizes the
absolute scalar double sum used in Lemma 6.5.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coefficient magnitudes, retained as complex coefficients for the existing convolution API. -/
def magnitude (a : Coeff p) : Coeff p :=
  ⟨fun k => (‖a k‖ : ℂ), (lp.memℓp a).mono' (by intro k; simp)⟩

omit [Fact (1 ≤ p)] in
@[simp] theorem magnitude_apply (a : Coeff p) (k : ℤ) : magnitude a k = (‖a k‖ : ℂ) := rfl

@[simp] theorem norm_magnitude (a : Coeff p) : ‖magnitude a‖ = ‖a‖ := by
  apply le_antisymm
  · apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro k; simp
  · apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro k; simp

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Exact absolute convolution row of the positive sandwich. -/
theorem norm_magnitude_sandwich_apply (a : Coeff q) (φ : Coeff p) (b : Coeff q) (f : Coeff p) (j : ℤ) :
    ‖convolutionSandwich (magnitude a) (magnitude φ) (magnitude b) (magnitude f) j‖ =
      ‖a j‖ * ∑' k : ℤ, ‖φ (j-k)‖ * (‖b k‖ * ‖f k‖) := by
  simp only [convolutionSandwich_apply, magnitude_apply, ← Complex.ofReal_mul,
    ← Complex.ofReal_tsum, Complex.norm_real]
  rw [Real.norm_of_nonneg (mul_nonneg (tsum_nonneg (fun _ => by positivity)) (norm_nonneg _)), mul_comm]
  apply congrArg (fun s : ℝ => ‖a j‖ * s)
  apply tsum_congr
  intro k
  rw [mul_comm ‖f k‖ ‖b k‖]

/-- The positive sandwich has the same uniform product norm bound as its original factors. -/
theorem norm_magnitude_sandwich_le (a : Coeff q) (φ : Coeff p) (b : Coeff q) (f : Coeff p) :
    ‖convolutionSandwich (magnitude a) (magnitude φ) (magnitude b) (magnitude f)‖ ≤
      ‖a‖ * ‖φ‖ * ‖b‖ * ‖f‖ := by
  simpa only [norm_magnitude] using norm_convolutionSandwich_apply_le (magnitude a) (magnitude φ) (magnitude b) (magnitude f)

end NLS.Coeff
