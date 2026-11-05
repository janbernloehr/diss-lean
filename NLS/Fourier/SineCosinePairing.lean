import NLS.Fourier.SineSquarePairing

/-! # Exact signed unit Fourier pairing with a sine-cosine product -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.ZakharovShabat
namespace NLS.Fourier

theorem sine_cosine_eq_wave_difference (n : ℤ) (x : ℝ) :
    sin ((n : ℂ)*(Real.pi : ℂ)*x)*cos ((n : ℂ)*(Real.pi : ℂ)*x) =
      (wave (2*n) x-wave (-(2*n)) x)/(4*I) := by
  have hp : wave (2*n) x = exp ((2*((n : ℂ)*(Real.pi : ℂ)*x))*I) := by
    unfold wave
    congr 1
    push_cast
    ring
  have hm : wave (-(2*n)) x = exp ((-(2*((n : ℂ)*(Real.pi : ℂ)*x)))*I) := by
    unfold wave
    congr 1
    push_cast
    ring
  rw [hp,hm,exp_mul_I,exp_mul_I,cos_neg,sin_neg,sin_two_mul]
  field_simp
  ring

theorem intervalL2_sine_cosine_pairing (u : IntervalL2) (n : ℤ) :
    (∫ s in (0 : ℝ)..1, u s*(sin ((n : ℂ)*(Real.pi : ℂ)*s)*cos ((n : ℂ)*(Real.pi : ℂ)*s))) =
      (intervalFourierCoefficient 1 u (-n)-intervalFourierCoefficient 1 u n)/(4*I) := by
  have hu : IntervalIntegrable u volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((Lp.memLp u).integrable (by norm_num))
  have hp := hu.mul_continuousOn (continuous_wave (2*n)).continuousOn
  have hm := hu.mul_continuousOn (continuous_wave (-(2*n))).continuousOn
  have hc (k : ℤ) : intervalFourierCoefficient 1 u k = ∫ s in (0 : ℝ)..1, u s*wave (-(2*k)) s := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),← unitFourierCoefficient_eq_fourierCoeffOn]
    rfl
  rw [hc (-n),hc n]
  simp only [mul_neg,neg_neg]
  calc
    _ = ∫ s in (0 : ℝ)..1, (u s*wave (2*n) s-u s*wave (-(2*n)) s)/(4*I) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [sine_cosine_eq_wave_difference]
      ring
    _ = _ := by rw [intervalIntegral.integral_div,intervalIntegral.integral_sub hp hm]

theorem integral_sine_cosine_unit (n : ℤ) (hn : n ≠ 0) :
    (∫ s in (0 : ℝ)..1, sin ((n : ℂ)*(Real.pi : ℂ)*s)*cos ((n : ℂ)*(Real.pi : ℂ)*s)) = 0 := by
  have hp : (∫ s in (0 : ℝ)..1, wave (2*n) s) = 0 :=
    (unitIntegral_even n).trans (if_neg hn)
  have hm : (∫ s in (0 : ℝ)..1, wave (-(2*n)) s) = 0 := by
    rw [show -(2*n) = 2*(-n) by ring]
    exact (unitIntegral_even (-n)).trans (if_neg (neg_ne_zero.mpr hn))
  calc
    _ = ∫ s in (0 : ℝ)..1, (wave (2*n) s-wave (-(2*n)) s)/(4*I) :=
      intervalIntegral.integral_congr (fun s _ => sine_cosine_eq_wave_difference n s)
    _ = _ := by
      rw [intervalIntegral.integral_div,intervalIntegral.integral_sub
        ((continuous_wave (2*n)).intervalIntegrable (μ := volume) 0 1)
        ((continuous_wave (-(2*n))).intervalIntegrable (μ := volume) 0 1),hp,hm,sub_self,zero_div]

end NLS.Fourier
