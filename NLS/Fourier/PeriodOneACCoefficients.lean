import NLS.Fourier.UnitIntervalDerivativeCoefficient
import NLS.Fourier.AbsoluteContinuousCoefficients
import NLS.Fourier.PeriodOneH1Norm

/-! # Original unit-period Fourier coefficients of rough periodic derivatives

An actual almost-everywhere derivative in L² determines the physical
2*pi*i*n multiplier. Absolute continuity and matching endpoint values
suffice; no smoothness or supplied periodic extension is assumed.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.Fourier

theorem memlp_periodOneCoefficient {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) : Memℓp (periodOneCoefficient f) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (hasSum_sq_periodOneCoefficient hf).summable

theorem periodOneCoefficient_deriv_of_ac {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfi : IntervalIntegrable (deriv f) volume 0 1) (n : ℤ) :
    periodOneCoefficient (deriv f) n =
      2*I*(Real.pi : ℂ)*n*periodOneCoefficient f n+f 1-f 0 := by
  have hw := (contDiff_wave (-(2*n))).contDiffOn.absolutelyContinuousOnInterval
    (a := (0 : ℝ)) (b := 1)
  have hwi : IntervalIntegrable (deriv (wave (-(2*n)))) volume 0 1 := by
    rw [deriv_wave]
    exact (continuous_const.mul (continuous_wave _)).intervalIntegrable 0 1
  have h := integral_mul_deriv_eq_complex hf hw hfi hwi
  have hw1 : wave (-(2*n)) 1 = 1 := by rw [show -(2*n) = 2*(-n) by ring,wave_even_at_one]
  simp only [deriv_wave,hw1,wave_at_zero,mul_one] at h
  have he : (fun t => f t*(I*(Real.pi : ℂ)*(-(2*n) : ℤ)*wave (-(2*n)) t)) =
      fun t => -(2*I*(Real.pi : ℂ)*n)*(f t*wave (-(2*n)) t) := by
    funext t
    push_cast
    ring
  rw [he,intervalIntegral.integral_const_mul] at h
  have hcoef (g : ℝ → ℂ) : periodOneCoefficient g n = unitFourierCoefficient g n :=
    (unitFourierCoefficient_eq_fourierCoeffOn g n).symm
  rw [hcoef,hcoef]
  unfold unitFourierCoefficient
  linear_combination h

theorem periodOneCoefficient_of_ac_derivative {f g : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x)
    (hend : f 1 = f 0) (n : ℤ) :
    periodOneCoefficient g n = 2*I*(Real.pi : ℂ)*n*periodOneCoefficient f n := by
  have he : deriv f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g := by
    filter_upwards [hd] with x hx
    exact hx.deriv
  have hi : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((hg.ae_eq he.symm).integrable (by norm_num))
  have hc : periodOneCoefficient (deriv f) n = periodOneCoefficient g n := by
    exact congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1) he) n
  rw [← hc,periodOneCoefficient_deriv_of_ac hf hi n,hend]
  ring

end NLS.Fourier
