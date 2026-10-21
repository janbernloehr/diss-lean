import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Exact signs for integer imaginary half-periods

The signed free carriers coincide, square to one, and give the exact multiplier for shifted hyperbolic sine.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- The hyperbolic sine vanishes at every integer imaginary half-period. -/
theorem sinh_int_pi_I_eq_zero (n : ℤ) : sinh (I*((Real.pi:ℂ)*n)) = 0 := by
  rw [mul_comm I,sinh_mul_I,mul_comm (Real.pi:ℂ),sin_int_mul_pi,zero_mul]

/-- The two signed free carriers coincide at every integer mode. -/
theorem exp_neg_int_pi_I_eq (n : ℤ) :
    exp (-I*((Real.pi:ℂ)*n)) = exp (I*((Real.pi:ℂ)*n)) := by
  have h := two_sinh (I*((Real.pi:ℂ)*n))
  rw [sinh_int_pi_I_eq_zero,mul_zero] at h
  rw [neg_mul]
  linear_combination h

/-- Each free half-period carrier squares to one. -/
theorem exp_int_pi_I_sq (n : ℤ) : (exp (I*((Real.pi:ℂ)*n)))^2 = 1 := by
  rw [pow_two]
  calc
    _ = exp (I*((Real.pi:ℂ)*n))*exp (-I*((Real.pi:ℂ)*n)) := by rw [exp_neg_int_pi_I_eq]
    _ = exp (I*((Real.pi:ℂ)*n)+(-I*((Real.pi:ℂ)*n))) := (exp_add _ _).symm
    _ = 1 := by rw [show I*((Real.pi:ℂ)*n)+(-I*((Real.pi:ℂ)*n)) = 0 by ring,exp_zero]

/-- Integer imaginary shifts multiply hyperbolic sine by the signed free carrier. -/
theorem sinh_add_int_pi_I_eq_exp (z : ℂ) (n : ℤ) :
    sinh (z+I*((Real.pi:ℂ)*n)) = exp (I*((Real.pi:ℂ)*n))*sinh z := by
  have hc : cosh (I*((Real.pi:ℂ)*n)) = exp (I*((Real.pi:ℂ)*n)) := by
    rw [cosh,← neg_mul,exp_neg_int_pi_I_eq]
    ring
  rw [sinh_add,sinh_int_pi_I_eq_zero,mul_zero,add_zero,hc,mul_comm]

end NLS.ComplexAnalysis
