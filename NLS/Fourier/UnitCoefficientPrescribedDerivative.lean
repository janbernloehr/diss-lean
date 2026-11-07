import NLS.Fourier.UnitIntervalWeakDerivative

/-! Unit Fourier integration by parts for a prescribed continuous
interior derivative. The ACTUAL endpoint defect is retained first. -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.Fourier

theorem unitFourierCoefficient_prescribed_derivative
    (f f1 : ℝ → ℂ) (hf : Continuous f) (hf1 : Continuous f1)
    (hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (f1 t) t) (k : ℤ) :
    unitFourierCoefficient f1 k=2*I*(Real.pi:ℂ)*k*unitFourierCoefficient f k+(f 1-f 0) := by
  have hD (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (fun x => f x*wave (-(2*k)) x)
        (f1 t*wave (-(2*k)) t-(2*I*(Real.pi:ℂ)*k)*(f t*wave (-(2*k)) t)) t := by
    have h := (hd t ht).mul (hasDerivAt_wave (-(2*k)) t)
    convert h using 1 <;> first | rfl | (push_cast; ring)
  have hA : IntervalIntegrable (fun x : ℝ => f1 x*wave (-(2*k)) x) volume 0 1 :=
    (hf1.mul (continuous_wave _)).intervalIntegrable 0 1
  have hB : IntervalIntegrable (fun x : ℝ => (2*I*(Real.pi:ℂ)*k)*(f x*wave (-(2*k)) x)) volume 0 1 :=
    (continuous_const.mul (hf.mul (continuous_wave _))).intervalIntegrable 0 1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    (hf.mul (continuous_wave _)).continuousOn hD (hA.sub hB)
  have hw : wave (-(2*k)) 1=1 := by rw [show -(2*k)=2*(-k) by ring,wave_even_at_one]
  dsimp only [Pi.mul_apply] at hi
  simp only [hw,wave_at_zero,mul_one] at hi
  rw [intervalIntegral.integral_sub hA hB,intervalIntegral.integral_const_mul] at hi
  change unitFourierCoefficient f1 k-(2*I*(Real.pi:ℂ)*k)*unitFourierCoefficient f k=f 1-f 0 at hi
  linear_combination hi

theorem unitFourierCoefficient_prescribed_periodic_derivative
    (f f1 : ℝ → ℂ) (hf : Continuous f) (hf1 : Continuous f1)
    (hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (f1 t) t) (hperiod : f 1=f 0) (k : ℤ) :
    unitFourierCoefficient f1 k=2*I*(Real.pi:ℂ)*k*unitFourierCoefficient f k := by
  rw [unitFourierCoefficient_prescribed_derivative f f1 hf hf1 hd k,hperiod,sub_self,add_zero]

end NLS.Fourier
