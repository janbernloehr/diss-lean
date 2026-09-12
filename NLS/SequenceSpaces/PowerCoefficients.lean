import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Powers of coefficient magnitudes

Positive real powers move `ℓᵖ` into `ℓ^(p/t)` with the exact norm identity.
The original exponent may be below one: no Banach-space instance is assumed.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- Raising magnitudes to a positive power divides the sequence exponent. -/
def normPower {p t : ℝ} (hp : 0 < p) (ht : 0 < t)
    (a : Coeff (ENNReal.ofReal p)) : Coeff (ENNReal.ofReal (p / t)) := by
  refine ⟨fun n => (‖a n‖ ^ t : ℝ), ?_⟩
  apply memℓp_gen
  have ha := (lp.memℓp a).summable (by simpa [ENNReal.toReal_ofReal hp.le] using hp)
  simpa only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal (div_pos hp ht).le,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ ht.ne'] using ha

@[simp] theorem normPower_apply {p t : ℝ} (hp : 0 < p) (ht : 0 < t)
    (a : Coeff (ENNReal.ofReal p)) (n : ℤ) :
    normPower hp ht a n = (‖a n‖ ^ t : ℝ) := rfl

/-- The exact norm identity also holds for positive exponents below one. -/
theorem norm_normPower {p t : ℝ} (hp : 0 < p) (ht : 0 < t)
    (a : Coeff (ENNReal.ofReal p)) : ‖normPower hp ht a‖ = ‖a‖ ^ t := by
  rw [lp.norm_eq_tsum_rpow (by simpa [ENNReal.toReal_ofReal (div_pos hp ht).le] using div_pos hp ht),
    lp.norm_eq_tsum_rpow (by simpa [ENNReal.toReal_ofReal hp.le] using hp)]
  simp only [normPower_apply, ENNReal.toReal_ofReal hp.le,
    ENNReal.toReal_ofReal (div_pos hp ht).le, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ ht.ne']
  rw [← Real.rpow_mul (tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  congr 1
  field_simp

end NLS.Coeff
