import NLS.Fourier.PeriodOneCoefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! Exact sine/cosine pairings for the unit-period coefficient convention.
All formulas are actual interval integrals with no reality assumption. -/
noncomputable section
open Complex MeasureTheory
namespace NLS.Fourier

theorem periodOneCoefficient_eq_wave_integral (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient f n = ∫ t in (0:ℝ)..1, f t*wave (-(2*n)) t := by
  rw [periodOneCoefficient,fourierCoeffOn_one,halfCoefficient,← mul_assoc]
  norm_num

theorem integral_periodOneSynthesis_wave (a : Coeff 1) (n : ℤ) :
    (∫ t in (0:ℝ)..1, periodOneSynthesis a t*wave (2*n) t) = a (-n) := by
  have h := periodOneCoefficient_synthesis a (-n)
  rw [periodOneCoefficient_eq_wave_integral] at h
  simpa only [mul_neg,neg_neg] using h

theorem integral_periodOneSynthesis (a : Coeff 1) :
    (∫ t in (0:ℝ)..1, periodOneSynthesis a t) = a 0 := by
  simpa only [mul_zero,wave_zero,mul_one,neg_zero] using integral_periodOneSynthesis_wave a 0

theorem cos_unit_wave (n : ℤ) (t : ℝ) :
    cos (2*(Real.pi:ℂ)*n*t) = (wave (2*n) t+wave (2*(-n)) t)/2 := by
  rw [Complex.cos,wave,wave]
  push_cast
  congr 2 <;> congr 1 <;> ring

theorem sin_unit_wave (n : ℤ) (t : ℝ) :
    sin (2*(Real.pi:ℂ)*n*t) = (wave (2*n) t-wave (2*(-n)) t)/(2*I) := by
  rw [Complex.sin,wave,wave]
  push_cast
  have hp : 2*(Real.pi:ℂ)*n*t*I = (Real.pi*I*(2*n))*t := by ring
  have hm : -(2*(Real.pi:ℂ)*n*t)*I = (Real.pi*I*(2*-n))*t := by ring
  rw [hp,hm]
  field_simp
  rw [I_sq]
  ring

theorem integral_periodOneSynthesis_cos (a : Coeff 1) (n : ℤ) :
    (∫ t in (0:ℝ)..1, periodOneSynthesis a t*cos (2*(Real.pi:ℂ)*n*t)) =
      (a n+a (-n))/2 := by
  have hp : IntervalIntegrable (fun t => periodOneSynthesis a t*wave (2*n) t) volume 0 1 :=
    ((continuous_periodOneSynthesis a).mul (continuous_wave (2*n))).intervalIntegrable 0 1
  have hm : IntervalIntegrable (fun t => periodOneSynthesis a t*wave (2*(-n)) t) volume 0 1 :=
    ((continuous_periodOneSynthesis a).mul (continuous_wave (2*(-n)))).intervalIntegrable 0 1
  calc
    _ = ∫ t in (0:ℝ)..1, (periodOneSynthesis a t*wave (2*n) t+
        periodOneSynthesis a t*wave (2*(-n)) t)/2 := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [cos_unit_wave]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_div,intervalIntegral.integral_add hp hm,
        integral_periodOneSynthesis_wave,integral_periodOneSynthesis_wave,neg_neg,add_comm]

theorem integral_periodOneSynthesis_sin (a : Coeff 1) (n : ℤ) :
    (∫ t in (0:ℝ)..1, periodOneSynthesis a t*sin (2*(Real.pi:ℂ)*n*t)) =
      (a (-n)-a n)/(2*I) := by
  have hp : IntervalIntegrable (fun t => periodOneSynthesis a t*wave (2*n) t) volume 0 1 :=
    ((continuous_periodOneSynthesis a).mul (continuous_wave (2*n))).intervalIntegrable 0 1
  have hm : IntervalIntegrable (fun t => periodOneSynthesis a t*wave (2*(-n)) t) volume 0 1 :=
    ((continuous_periodOneSynthesis a).mul (continuous_wave (2*(-n)))).intervalIntegrable 0 1
  calc
    _ = ∫ t in (0:ℝ)..1, (periodOneSynthesis a t*wave (2*n) t-
        periodOneSynthesis a t*wave (2*(-n)) t)/(2*I) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [sin_unit_wave]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_div,intervalIntegral.integral_sub hp hm,
        integral_periodOneSynthesis_wave,integral_periodOneSynthesis_wave,neg_neg]

theorem integral_periodOneSynthesis_sin_sq (a : Coeff 1) (n : ℤ) :
    2*(∫ t in (0:ℝ)..1, periodOneSynthesis a t*sin ((Real.pi:ℂ)*n*t)^2) =
      a 0-(a n+a (-n))/2 := by
  have hpoint (t : ℝ) :
      2*(periodOneSynthesis a t*sin ((Real.pi:ℂ)*n*t)^2) =
        periodOneSynthesis a t-periodOneSynthesis a t*cos (2*(Real.pi:ℂ)*n*t) := by
    rw [show 2*(Real.pi:ℂ)*n*(t:ℂ)=2*((Real.pi:ℂ)*n*t) by ring,Complex.cos_two_mul]
    have h := Complex.sin_sq_add_cos_sq ((Real.pi:ℂ)*n*t)
    linear_combination 2*periodOneSynthesis a t*h
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [hpoint]
  have hfc : Continuous (periodOneSynthesis a) := continuous_periodOneSynthesis a
  rw [intervalIntegral.integral_sub ((continuous_periodOneSynthesis a).intervalIntegrable 0 1)
    (by exact (by fun_prop : Continuous (fun t : ℝ =>
      periodOneSynthesis a t*cos (2*(Real.pi:ℂ)*n*t))).intervalIntegrable 0 1),
    integral_periodOneSynthesis,integral_periodOneSynthesis_cos]

end NLS.Fourier
