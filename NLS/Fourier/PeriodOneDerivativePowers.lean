import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra
import NLS.FunctionalAnalysis.PeriodicIntegrationByParts

/-! # Exact unit-period coefficients of all iterated physical derivatives -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ContDiff
namespace NLS.Fourier

theorem periodOneCoefficient_iteratedDeriv_of_smooth_periodic (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (m : ℕ) (n : ℤ) :
    periodOneCoefficient (iteratedDeriv m f) n=
      (2*I*(Real.pi : ℂ)*n)^m*periodOneCoefficient f n := by
  induction m with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ m ih =>
    rw [iteratedDeriv_succ,periodOneCoefficient_deriv_of_smooth_periodic _
      (NLS.FunctionalAnalysis.contDiff_iteratedDeriv f hf m)
      (NLS.FunctionalAnalysis.periodic_iteratedDeriv f 1 hp m),ih,pow_succ]
    ring

end NLS.Fourier
