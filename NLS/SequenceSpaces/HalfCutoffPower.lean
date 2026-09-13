import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Power decay at an integer half cutoff

For `N≥2`, the integer half cutoff is at least `N/3`. Every decay exponent
between zero and one therefore loses at most a factor three.
-/

namespace NLS

/-- Replacing the integer half cutoff by the full cutoff costs at most three. -/
theorem one_div_halfCutoff_rpow_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) :
    1 / ((N/2 : ℕ) : ℝ)^δ ≤ 3 / (N : ℝ)^δ := by
  have hM : (0 : ℝ) < (N/2 : ℕ) := by exact_mod_cast (show 0 < N/2 by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hM _) (Real.rpow_pos_of_pos hNr _)).mpr
  simp only [one_mul]
  calc
    (N : ℝ)^δ ≤ (3*((N/2 : ℕ) : ℝ))^δ := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hδ0
      exact_mod_cast (show N ≤ 3*(N/2) by omega)
    _ = (3 : ℝ)^δ * ((N/2 : ℕ) : ℝ)^δ := Real.mul_rpow (by norm_num) hM.le
    _ ≤ 3 * ((N/2 : ℕ) : ℝ)^δ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hδ1

end NLS
