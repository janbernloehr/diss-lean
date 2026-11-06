import NLS.KdV.SquaredCoshDerivative
import NLS.KdV.ClassicalBranchPrimitive
import NLS.ZakharovShabat.FreeDerivativeZeroCounts
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot

/-! # Noncriticality of squared cosh on its first spectral disc -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem deriv_squaredCosh_ne_zero_of_norm_lt_pi_sq (w : ℂ) (hw : ‖w‖ < Real.pi^2) :
    deriv squaredCosh w ≠ 0 := by
  by_cases hw0 : w = 0
  · subst w
    rw [hasDerivAt_squaredCosh_zero.deriv]
    norm_num
  intro hd
  let s := Complex.sqrt w
  have hs : s^2 = w := NLS.ComplexAnalysis.sq_sqrt w
  have hn : ‖s‖^2 = ‖w‖ := by rw [← norm_pow,hs]
  have hsp : ‖s‖ < Real.pi := by nlinarith [norm_nonneg s,Real.pi_pos]
  have hz : sinh s = 0 := by
    rw [← deriv_squaredCosh_sq_mul,hs,hd,zero_mul]
  have hsin : -2*sin (s*I) = 0 := by rw [sin_mul_I,hz,zero_mul,mul_zero]
  have he := NLS.ZakharovShabat.free_derivative_zero_eq_center hsp 0
    (z := s*I) (by simp only [Int.cast_zero,mul_zero,mem_closedBall,dist_zero_right,norm_mul,norm_I,mul_one,le_refl]) hsin
  have hs0 : s = 0 := (mul_eq_zero.mp (by simpa only [Int.cast_zero,mul_zero] using he)).resolve_right I_ne_zero
  exact hw0 (by rw [← hs,hs0];norm_num)

end NLS.KdV
