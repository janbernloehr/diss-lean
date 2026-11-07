import NLS.SequenceSpaces.PeriodOneKdVNativeVector
import NLS.Fourier.PeriodOneDerivativePowers
import NLS.Fourier.PeriodOneAffineCoefficients
import NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities

/-! # The native conservative KdV vector is the literal physical PDE

The exact unit-period third derivative and infinite product convolution
identify every signed coefficient with -u_xxx+6*u*u_x at any actual
smooth periodic representative. No finite-gap condition is used here.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier
open NLS.Articles.KdVKdV2Frequencies
open scoped ContDiff
namespace NLS.KdV

theorem kdvRHS_conservative (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    kdvRHS f=fun x => -iteratedDeriv 3 f x+3*deriv (f*f) x := by
  funext x
  have hd := ((hf.differentiable (by simp) x).hasDerivAt.mul
    (hf.differentiable (by simp) x).hasDerivAt).deriv
  change deriv (f*f) x=deriv f x*f x+f x*deriv f x at hd
  rw [kdvRHS,iteratedDeriv_one,hd]
  ring

theorem periodOneKdVNativeVector_coefficients
    (a : WeightedCoeff (Weight.sobolev 4) 2) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ n : ℤ, a.val n=periodOneCoefficient f n) (n : ℤ) :
    (periodOneKdVNativeVector a).val n=periodOneCoefficient (kdvRHS f) n := by
  have hprod : Function.Periodic (f*f) 1 := by
    intro x
    change f (x+1)*f (x+1)=f x*f x
    rw [hp]
  have hff : ContDiff ℝ ∞ (f*f) := hf.mul hf
  have hlin := periodOneCoefficient_affine (-iteratedDeriv 3 f) (deriv (f*f))
    (NLS.FunctionalAnalysis.contDiff_iteratedDeriv f hf 3).continuous.neg
    ((contDiff_infty_iff_deriv.mp hff).2.continuous) 3 n
  change periodOneCoefficient (fun x => -iteratedDeriv 3 f x+3*deriv (f*f) x) n=
    periodOneCoefficient (-iteratedDeriv 3 f) n+3*periodOneCoefficient (deriv (f*f)) n at hlin
  rw [periodOneKdVNativeVector_apply,kdvRHS_conservative f hf,hlin,
    periodOneCoefficient_neg,periodOneCoefficient_iteratedDeriv_of_smooth_periodic f hf hp,
    periodOneCoefficient_deriv_of_smooth_periodic (f*f) hff hprod,
    periodOneCoefficient_mul_of_smooth_periodic f f hf hf hp hp]
  simp_rw [hc]
  ring

end NLS.KdV
