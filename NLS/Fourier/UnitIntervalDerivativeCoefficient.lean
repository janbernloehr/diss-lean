import NLS.Fourier.IntervalBilinearParseval
import NLS.Fourier.SobolevDerivative

/-! # The period-one multiplier for a physical interval derivative

Only an actual derivative on the unit interval and matching endpoint
values are required. The function need not be globally smooth or have
a supplied periodic extension.
-/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.Fourier

theorem unitFourierCoefficient_of_hasDerivAt (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hend : f 1 = f 0) (n : ℤ) :
    unitFourierCoefficient g n = 2*I*(Real.pi : ℂ)*n*unitFourierCoefficient f n := by
  let c : ℂ := I*(Real.pi : ℂ)*(-(2*n) : ℤ)
  have hc : Continuous (fun t => g t*wave (-(2*n)) t+f t*(c*wave (-(2*n)) t)) := by
    exact (hg.mul (continuous_wave _)).add (hf.mul (continuous_const.mul (continuous_wave _)))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (hf.mul (continuous_wave _)).continuousOn
    (fun t ht => (hd t ⟨ht.1.le,ht.2.le⟩).mul (hasDerivAt_wave (-(2*n)) t))
    (hc.intervalIntegrable 0 1)
  have hw : wave (-(2*n)) 1 = 1 := by
    rw [show -(2*n) = 2*(-n) by ring,wave_even_at_one]
  dsimp only [Pi.mul_apply] at hi
  rw [hw,wave_at_zero,mul_one,mul_one,hend,sub_self] at hi
  have he : (fun t => g t*wave (-(2*n)) t+f t*(c*wave (-(2*n)) t)) =
      fun t => g t*wave (-(2*n)) t+c*(f t*wave (-(2*n)) t) := by funext t; ring
  change (∫ t in (0 : ℝ)..1, g t*wave (-(2*n)) t+f t*(c*wave (-(2*n)) t)) = 0 at hi
  have hgi : IntervalIntegrable (fun t => g t*wave (-(2*n)) t) volume 0 1 :=
    (hg.mul (continuous_wave _)).intervalIntegrable 0 1
  have hfi : IntervalIntegrable (fun t => c*(f t*wave (-(2*n)) t)) volume 0 1 :=
    (continuous_const.mul (hf.mul (continuous_wave _))).intervalIntegrable 0 1
  rw [he,intervalIntegral.integral_add hgi hfi,
    intervalIntegral.integral_const_mul] at hi
  change unitFourierCoefficient g n+c*unitFourierCoefficient f n = 0 at hi
  dsimp only [c] at hi
  push_cast at hi
  linear_combination hi

end NLS.Fourier
