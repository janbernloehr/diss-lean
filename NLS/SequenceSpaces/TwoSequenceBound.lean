import NLS.SequenceSpaces.FunctionOrZero
import NLS.SequenceSpaces.SandwichMajorant

/-! # Realizing a sequence dominated by two coefficient sequences -/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A sum of two `ℓᵖ` majorants proves membership and bounds the actual
sequence realization; the constructor's fallback cannot occur. -/
theorem memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
    (f : ℤ → ℂ) (a b : Coeff p) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C*(‖a n‖+‖b n‖)) :
    Memℓp f p ∧ ‖ofFunctionOrZero p f‖ ≤ C*(‖a‖+‖b‖) := by
  let E : Coeff p := (C:ℂ) • (magnitude a+magnitude b)
  have hE n : ‖E n‖ = C*(‖a n‖+‖b n‖) := by
    simp only [E,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,
      magnitude_apply,← Complex.ofReal_add,← Complex.ofReal_mul,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ C*(‖a n‖+‖b n‖))]
  have hpoint n : ‖f n‖ ≤ ‖E n‖ := (hf n).trans_eq (hE n).symm
  have hmem : Memℓp f p := (lp.memℓp E).mono' hpoint
  refine ⟨hmem,?_⟩
  calc
    ‖ofFunctionOrZero p f‖ ≤ ‖E‖ := lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (by intro n; rw [ofFunctionOrZero_apply_of_mem p f hmem n]; exact hpoint n)
    _ = C*‖magnitude a+magnitude b‖ := by
      rw [show ‖E‖ = ‖(C:ℂ)‖*‖magnitude a+magnitude b‖ from norm_smul _ _,
        Complex.norm_real,Real.norm_of_nonneg hC]
    _ ≤ C*(‖a‖+‖b‖) := mul_le_mul_of_nonneg_left
      (by simpa only [norm_magnitude] using norm_add_le (magnitude a) (magnitude b)) hC

end NLS.Coeff
