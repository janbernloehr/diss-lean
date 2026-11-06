import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra

/-! # Original unit-period coefficients of affine physical variations -/
noncomputable section
set_option autoImplicit false
open Complex MeasureTheory
namespace NLS.Fourier

theorem periodOneCoefficient_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient (fun x => c*f x) n = c*periodOneCoefficient f n := by
  calc
    _ = unitFourierCoefficient (fun x => c*f x) n :=
      (unitFourierCoefficient_eq_fourierCoeffOn _ n).symm
    _ = c*unitFourierCoefficient f n := by
      simp only [unitFourierCoefficient,mul_assoc,intervalIntegral.integral_const_mul]
    _ = _ := congrArg (fun z : ℂ => c*z) (unitFourierCoefficient_eq_fourierCoeffOn f n)

theorem periodOneCoefficient_affine (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (c : ℂ) (n : ℤ) : periodOneCoefficient (fun x => f x+c*g x) n =
      periodOneCoefficient f n+c*periodOneCoefficient g n := by
  change periodOneCoefficient (f+(fun x => c*g x)) n = _
  rw [periodOneCoefficient_add f (fun x => c*g x) hf (continuous_const.mul hg),
    periodOneCoefficient_const_mul]

end NLS.Fourier
