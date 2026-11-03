import Mathlib.Analysis.Complex.Basic

/-! # Squared-coordinate gaps of an unordered pair

The estimate needs only membership in the pair, and includes repetitions.
A common energy translation cancels exactly.
-/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem norm_shifted_square_gap_le_of_mem_pair (a b x y c : ℂ) (A : ℝ)
    (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A)
    (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) :
    ‖(x^2-c)-(y^2-c)‖ ≤ 2*A*‖b-a‖ := by
  have hsub : ‖a^2-b^2‖ ≤ 2*A*‖b-a‖ := by
    calc
      _ = ‖a-b‖*‖a+b‖ := by rw [sq_sub_sq,norm_mul];ring
      _ ≤ ‖a-b‖*(A+A) := mul_le_mul_of_nonneg_left
        ((norm_add_le a b).trans (add_le_add ha hb)) (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev a b];ring
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp only [sub_self,norm_zero]
    positivity
  · simpa only [sub_sub_sub_cancel_right] using hsub
  · rw [norm_sub_rev]
    simpa only [sub_sub_sub_cancel_right] using hsub
  · simp only [sub_self,norm_zero]
    positivity

end NLS.ComplexAnalysis
