import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reciprocal perturbations away from the unit disc

Displacements of norm at most one half preserve a lower bound on a denominator
of norm at least one. Subtracting the unperturbed reciprocal gains a second
power of decay, uniformly over arbitrary complex displacements.
-/

noncomputable section
namespace NLS.ComplexAnalysis

/-- A half-unit perturbation preserves half the norm of a denominator of norm at least one. -/
theorem norm_sub_ge_half {a t : ℂ} (ha : 1 ≤ ‖a‖) (ht : ‖t‖ ≤ (1 : ℝ)/2) :
    ‖a‖/2 ≤ ‖a-t‖ := by
  have h := norm_sub_norm_le a t
  linarith

/-- The reciprocal of a perturbed denominator has twice the usual reciprocal bound. -/
theorem norm_inv_sub_le {a t : ℂ} (ha : 1 ≤ ‖a‖) (ht : ‖t‖ ≤ (1 : ℝ)/2) :
    ‖(a-t)⁻¹‖ ≤ 2/‖a‖ := by
  rw [norm_inv]
  have h := inv_anti₀ (by linarith : 0 < ‖a‖/2) (norm_sub_ge_half ha ht)
  simpa [div_eq_mul_inv] using h

/-- The reciprocal difference gains a square denominator under a half-unit perturbation. -/
theorem norm_inv_sub_sub_inv_le {a t : ℂ} (ha : 1 ≤ ‖a‖) (ht : ‖t‖ ≤ (1 : ℝ)/2) :
    ‖(a-t)⁻¹-a⁻¹‖ ≤ ‖a‖⁻¹^2 := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (by linarith)
  have hat : a-t ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by linarith) (norm_sub_ge_half ha ht))
  have he : (a-t)⁻¹-a⁻¹ = t*a⁻¹*(a-t)⁻¹ := by field_simp; ring
  rw [he, norm_mul, norm_mul, norm_inv]
  have h := mul_le_mul ht (norm_inv_sub_le ha ht) (norm_nonneg ((a-t)⁻¹)) (by norm_num : (0 : ℝ) ≤ 1/2)
  have hi : 0 ≤ ‖a‖⁻¹ := inv_nonneg.mpr (norm_nonneg a)
  have hh := mul_le_mul_of_nonneg_right h hi
  simp only [div_eq_mul_inv] at hh
  nlinarith

end NLS.ComplexAnalysis
