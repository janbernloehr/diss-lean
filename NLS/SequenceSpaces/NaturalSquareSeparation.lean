import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Natural quadratic spectral centers have separation at least the sum of their indices. -/

noncomputable section
set_option autoImplicit false
namespace NLS.SequenceSpaces
theorem nat_square_separation_ge_sum (m n : ℕ) (hmn : m ≠ n) :
    (m : ℝ)+n ≤ |(m : ℝ)^2-(n : ℝ)^2| := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hmnR : (m : ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hlt)
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ n-m by linarith)
      (show (0 : ℝ) ≤ n+m by positivity)
    rw [abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) m] : (m : ℝ)^2-n^2 ≤ 0)]
    nlinarith
  · have hmnR : (n : ℝ)+1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hgt)
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ m-n by linarith)
      (show (0 : ℝ) ≤ m+n by positivity)
    rw [abs_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n] : 0 ≤ (m : ℝ)^2-n^2)]
    nlinarith


end NLS.SequenceSpaces
