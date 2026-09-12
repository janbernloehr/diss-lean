import NLS.Fourier.SobolevDerivative
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-!
# Fourier coefficients of absolutely continuous functions

Integration by parts gives the derivative multiplier and the endpoint jump.
The formula includes the zero frequency and keeps the period-two factor `1/2`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

@[fun_prop] theorem contDiff_wave (n : ℤ) : ContDiff ℝ 1 (wave n) := by
  have hcast : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  unfold wave
  fun_prop

@[simp] theorem deriv_wave (n : ℤ) :
    deriv (wave n) = fun x => Complex.I * (Real.pi : ℂ) * n * wave n x := by
  funext x
  exact (hasDerivAt_wave n x).deriv

/-- The derivative coefficient includes the endpoint jump for a nonperiodic function. -/
theorem periodTwoCoefficient_deriv_of_ac {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 2)
    (hfi : IntervalIntegrable (deriv f) volume 0 2) (n : ℤ) :
    periodTwoCoefficient (deriv f) n =
      Complex.I * (Real.pi : ℂ) * n * periodTwoCoefficient f n + (f 2 - f 0) / 2 := by
  have hw := (contDiff_wave (-n)).contDiffOn.absolutelyContinuousOnInterval
    (a := (0 : ℝ)) (b := 2)
  have hwi : IntervalIntegrable (deriv (wave (-n))) volume 0 2 := by
    rw [deriv_wave]
    exact (continuous_const.mul (continuous_wave (-n))).intervalIntegrable 0 2
  have h := FunctionalAnalysis.integral_mul_deriv_eq_complex hf hw hfi hwi
  have hw2 : wave (-n) 2 = 1 := by
    have ht := wave_reflect (-n) 0
    simpa only [sub_zero, wave_at_zero] using ht
  simp only [deriv_wave, hw2, wave_at_zero, mul_one] at h
  have he : (fun t => f t * (Complex.I * (Real.pi : ℂ) * (-n : ℤ) * wave (-n) t)) =
      fun t => -(Complex.I * (Real.pi : ℂ) * n) * (f t * wave (-n) t) := by
    funext t
    push_cast
    ring
  rw [he, intervalIntegral.integral_const_mul] at h
  unfold periodTwoCoefficient
  linear_combination (1 / 2 : ℂ) * h

/-- Matching endpoints remove the boundary term, at every integer frequency. -/
theorem periodTwoCoefficient_deriv_of_ac_periodic {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 2)
    (hfi : IntervalIntegrable (deriv f) volume 0 2) (hend : f 2 = f 0) (n : ℤ) :
    periodTwoCoefficient (deriv f) n = Complex.I * (Real.pi : ℂ) * n * periodTwoCoefficient f n := by
  rw [periodTwoCoefficient_deriv_of_ac hf hfi n, hend]
  simp

/-- Parseval makes the normalized interval coefficients square summable. -/
theorem memlp_periodTwoCoefficient {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) : Memℓp (periodTwoCoefficient f) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (hasSum_sq_periodTwoCoefficient hf).summable

end NLS.Fourier
