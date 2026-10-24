import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Explicit product bounds for the two-by-two entrywise matrix norm -/
noncomputable section
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.Elementwise
namespace NLS.FunctionalAnalysis

/-- Matrix multiplication has the explicit dimension factor in the entrywise norm. -/
theorem norm_finTwo_matrix_mul_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖A*B‖ ≤ 2*‖A‖*‖B‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  have h (k : Fin 2) : ‖A i k*B k j‖ ≤ ‖A‖*‖B‖ := by
    rw [norm_mul]
    exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
      (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  exact (norm_add_le _ _).trans (by nlinarith [h 0,h 1])

/-- Three matrix factors have a bound suited to a projected fundamental kernel. -/
theorem norm_finTwo_matrix_triple_le (A P B : Matrix (Fin 2) (Fin 2) ℂ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : ‖A‖ ≤ C) (hP : ‖P‖ ≤ D)
    (hB : ‖B‖ ≤ C) : ‖A*P*B‖ ≤ 4*C^2*D := by
  have hAP : ‖A*P‖ ≤ 2*C*D :=
    (norm_finTwo_matrix_mul_le A P).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hP (norm_nonneg _) (by positivity))
  calc
    ‖A*P*B‖ ≤ 2*‖A*P‖*‖B‖ := norm_finTwo_matrix_mul_le _ _
    _ ≤ 2*(2*C*D)*C :=
      mul_le_mul (mul_le_mul_of_nonneg_left hAP (by norm_num)) hB (norm_nonneg _) (by positivity)
    _ = 4*C^2*D := by ring

end NLS.FunctionalAnalysis
