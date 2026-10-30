import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Explicit power-triangle constant

The two-term norm estimate retains the factor 2^(p-1) for every finite
Banach coefficient exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Explicit positive constant for the two remaining-row terms. -/
theorem norm_add_rpow_le_two_mul (hp : p ≠ ⊤) (x y : Coeff p) :
    ‖x+y‖ ^ p.toReal ≤ (2:ℝ) ^ (p.toReal-1) * (‖x‖ ^ p.toReal+‖y‖ ^ p.toReal) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa using (ENNReal.toReal_le_toReal (by simp) hp).mpr (Fact.out : 1 ≤ p)
  have hsum : (‖x‖+‖y‖) ^ p.toReal ≤
      (2:ℝ) ^ (p.toReal-1) * (‖x‖ ^ p.toReal+‖y‖ ^ p.toReal) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖x‖₊ ‖y‖₊ hp1
  exact (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) (by positivity)).trans hsum

end NLS.Coeff
