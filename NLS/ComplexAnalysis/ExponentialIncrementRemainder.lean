import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # A uniform exponential increment remainder

A quadratic exponential remainder combined with a first-order carrier error yields the required inverse-power estimate.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- Linearizing a small exponential increment about a nearby carrier
gains one order beyond the increment, including the zeroth-order case. -/
theorem norm_exp_increment_sub_linear_le
    (u v e : ℂ) (N : ℕ) (r A B C : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hu : ‖exp u‖ ≤ B) (hue : ‖exp u-e‖ ≤ A*r)
    (hv : ‖v‖ ≤ C*r^(N+1)) :
    ‖exp (u+v)-exp u-e*v‖ ≤ (A*C+B*C^2*Real.exp C)*r^(N+2) := by
  have hvC : ‖v‖ ≤ C := hv.trans (mul_le_of_le_one_right hC (pow_le_one₀ hr hr1))
  have he : ‖exp v-1-v‖ ≤ C^2*Real.exp C*r^(N+2) := by
    have h := norm_exp_sub_sum_le_norm_mul_exp v 2
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,
      Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,zero_add] at h
    rw [show exp v-1-v = exp v-(1+v) by ring]
    apply h.trans
    calc
      _ ≤ (C*r^(N+1))^2*Real.exp C := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hv 2) (Real.exp_le_exp.mpr hvC)
        (Real.exp_pos _).le (by positivity)
      _ = C^2*Real.exp C*r^((N+1)*2) := by rw [mul_pow,pow_mul]; ring
      _ ≤ C^2*Real.exp C*r^(N+2) := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr hr1 (by omega)) (by positivity)
  have hid : exp (u+v)-exp u-e*v = (exp u-e)*v+exp u*(exp v-1-v) := by
    rw [exp_add]
    ring
  rw [hid]
  calc
    _ ≤ ‖(exp u-e)*v‖+‖exp u*(exp v-1-v)‖ := norm_add_le _ _
    _ = ‖exp u-e‖*‖v‖+‖exp u‖*‖exp v-1-v‖ := by simp only [norm_mul]
    _ ≤ (A*r)*(C*r^(N+1))+B*(C^2*Real.exp C*r^(N+2)) :=
      add_le_add (mul_le_mul hue hv (norm_nonneg _) (by positivity))
        (mul_le_mul hu he (norm_nonneg _) hB)
    _ = _ := by rw [show N+2 = (N+1)+1 by omega,pow_succ]; ring

end NLS.ComplexAnalysis
