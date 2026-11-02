import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra

/-! # Original period-one Fourier coefficients and linear physical fields -/
noncomputable section
set_option autoImplicit false
namespace NLS.Fourier

theorem periodOneCoefficient_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient (fun x => c*f x) n = c*periodOneCoefficient f n :=
  fourierCoeffOn.const_smul _ _ _ _

theorem periodOneCoefficient_sub (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    periodOneCoefficient (f-g) n = periodOneCoefficient f n-periodOneCoefficient g n := by
  rw [sub_eq_add_neg,periodOneCoefficient_add f (-g) hf hg.neg,periodOneCoefficient_neg,sub_eq_add_neg]

end NLS.Fourier
