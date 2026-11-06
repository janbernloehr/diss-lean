import NLS.ComplexAnalysis.LocalSinhComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! # Quantitative inversion on the full central imaginary phase strip -/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem norm_imaginary_phase_le_cosh_shift (r : ℝ) (hr : Real.cos r = 0)
    (z : ℂ) (hz : z.re = 0) (hstrip : |z.im| ≤ Real.pi/2) :
    ‖z‖ ≤ Real.pi/4 * ‖2*cosh (-I*r+z)‖ := by
  have hzero : cosh (-I*(r : ℂ)) = 0 := by
    rw [neg_mul, cosh_neg, mul_comm I, cosh_mul_I, ← ofReal_cos, hr, ofReal_zero]
  have hcosh := norm_cosh_shift_sub r hr z 0
  simp only [add_zero, hzero, sub_zero, sinh_zero] at hcosh
  have hrepr : z = (z.im : ℂ) * I := by apply Complex.ext <;> simp [hz]
  have hsin : ‖sinh z‖ = |Real.sin z.im| := by
    calc
      ‖sinh z‖ = ‖sinh ((z.im : ℂ)*I)‖ := congrArg (fun w => ‖sinh w‖) hrepr
      _ = _ := by rw [sinh_mul_I, norm_mul, norm_I, mul_one, ← ofReal_sin, norm_real, Real.norm_eq_abs]
  have hnorm : ‖z‖ = |z.im| := by
    calc
      ‖z‖ = ‖(z.im : ℂ)*I‖ := congrArg norm hrepr
      _ = _ := by rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  have hb := Real.mul_abs_le_abs_sin hstrip
  rw [← hsin, ← hnorm, div_mul_eq_mul_div] at hb
  have hh := (div_le_iff₀ Real.pi_pos).mp hb
  rw [norm_mul, norm_ofNat, hcosh]
  nlinarith

end NLS.ComplexAnalysis
