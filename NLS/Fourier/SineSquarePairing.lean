import NLS.Fourier.UnitIntervalL2Equiv
import NLS.Fourier.IntervalBilinearParseval
import Mathlib.Analysis.Complex.Trigonometric

/-! # Exact unit-period Fourier pairing with a sine square -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.ZakharovShabat
namespace NLS.Fourier

theorem wave_pair_eq_cos_double (n : ℤ) (x : ℝ) :
    wave (2*n) x+wave (-(2*n)) x = 2*cos (2*((n : ℂ)*(Real.pi : ℂ)*x)) := by
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
  rw [hp,hm,exp_mul_I,exp_mul_I,cos_neg,sin_neg]
  ring

theorem sine_square_eq_wave_pair (n : ℤ) (x : ℝ) :
    sin ((n : ℂ)*(Real.pi : ℂ)*x)^2 = (2-wave (2*n) x-wave (-(2*n)) x)/4 := by
  have h := wave_pair_eq_cos_double n x
  rw [cos_two_mul_eq_one_sub] at h
  linear_combination (1/4 : ℂ)*h

theorem intervalL2_sine_square_pairing (u : IntervalL2) (n : ℤ) :
    (∫ s in (0 : ℝ)..1, u s*sin ((n : ℂ)*(Real.pi : ℂ)*s)^2) =
      (2*intervalFourierCoefficient 1 u 0-intervalFourierCoefficient 1 u n-
        intervalFourierCoefficient 1 u (-n))/4 := by
  have hu : IntervalIntegrable u volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((Lp.memLp u).integrable (by norm_num))
  have hp := hu.mul_continuousOn (continuous_wave (2*n)).continuousOn
  have hm := hu.mul_continuousOn (continuous_wave (-(2*n))).continuousOn
  have hc (k : ℤ) : intervalFourierCoefficient 1 u k = ∫ s in (0 : ℝ)..1, u s*wave (-(2*k)) s := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),← unitFourierCoefficient_eq_fourierCoeffOn]
    rfl
  rw [hc 0,hc n,hc (-n)]
  simp only [mul_zero,neg_zero,wave_zero,mul_one,mul_neg,neg_neg]
  calc
    _ = ∫ s in (0 : ℝ)..1, ((2*u s-u s*wave (-(2*n)) s)-u s*wave (2*n) s)/4 := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [sine_square_eq_wave_pair]
      ring
    _ = _ := by rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub ((hu.const_mul 2).sub hm) hp,
      intervalIntegral.integral_sub (hu.const_mul 2) hm,intervalIntegral.integral_const_mul]

theorem integral_sine_square_unit (n : ℤ) (hn : n ≠ 0) :
    (∫ s in (0 : ℝ)..1, sin ((n : ℂ)*(Real.pi : ℂ)*s)^2) = (1 : ℂ)/2 := by
  have hp : (∫ s in (0 : ℝ)..1, wave (2*n) s) = 0 := by
    exact (unitIntegral_even n).trans (if_neg hn)
  have hm : (∫ s in (0 : ℝ)..1, wave (-(2*n)) s) = 0 := by
    rw [show -(2*n) = 2*(-n) by ring]
    exact (unitIntegral_even (-n)).trans (if_neg (neg_ne_zero.mpr hn))
  have hip := (continuous_wave (2*n)).intervalIntegrable (μ := volume) 0 1
  have him := (continuous_wave (-(2*n))).intervalIntegrable (μ := volume) 0 1
  calc
    _ = ∫ s in (0 : ℝ)..1, (2-wave (2*n) s-wave (-(2*n)) s)/4 :=
      intervalIntegral.integral_congr (fun s _ => sine_square_eq_wave_pair n s)
    _ = _ := by
      rw [intervalIntegral.integral_div,intervalIntegral.integral_sub
        (intervalIntegrable_const.sub hip) him,
        intervalIntegral.integral_sub intervalIntegrable_const hip,hp,hm,intervalIntegral.integral_const]
      norm_num

end NLS.Fourier
