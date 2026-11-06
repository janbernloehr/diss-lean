import NLS.Articles.KdVKdV2Frequencies.SmoothPhysicalHamiltonianVariation
import NLS.Articles.KdVKdV2Frequencies.NativeSourceFiniteActionVariation
import NLS.ComplexAnalysis.AffineLineDerivative
import NLS.Fourier.PeriodOneAffineCoefficients

/-! # The actual native differential is the independent physical Euler covector

Every affine complex native variation agrees with its actual smooth
physical period integral before derivatives are compared. No action or
spectral Hamiltonian definition is used in these covector identities.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.KdV NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

/-- Native affine variations retain the literal original physical Fourier coefficients. -/
theorem native_affine_physical_coefficients (m : ℕ) (q h : ScalarSobolev m)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hq : ∀ n : ℤ, q.val n=periodOneCoefficient f n)
    (hh : ∀ n : ℤ, h.val n=periodOneCoefficient g n) (c : ℂ) (n : ℤ) :
    (q+c • h).val n=periodOneCoefficient (fun x => f x+c*g x) n := by
  change q.val n+c*h.val n = _
  rw [hq n,hh n,periodOneCoefficient_affine f g hf hg]

/-- The actual complex native H1 Frechet covector is its independent
physical variational gradient on every smooth physical direction. -/
theorem fderiv_nativeKdVHamiltonian_physical (q h : ScalarSobolev 1) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (hq : ∀ n : ℤ, q.val n=periodOneCoefficient f n)
    (hh : ∀ n : ℤ, h.val n=periodOneCoefficient g n) :
    (fderiv ℂ nativeKdVHamiltonian q) h =
      ∫ x in (0 : ℝ)..1, g x*DifferentialPolynomial.evaluate f 0 kdvGradient x := by
  have hd := NLS.ComplexAnalysis.hasDerivAt_comp_affine_line nativeKdVHamiltonian q h
    (analyticAt_nativeKdVHamiltonian q).differentiableAt
  have he : (fun c : ℂ => nativeKdVHamiltonian (q+c • h)) =
      fun c : ℂ => classicalHamiltonian (fun x => f x+c*g x) := by
    funext c
    exact nativeKdVHamiltonian_eq_of_coefficients _ _
      (hf.continuous.add (continuous_const.mul hg.continuous))
      (fun x => by rw [hpf x,hpg x]) (native_affine_physical_coefficients 1 q h f g hf.continuous hg.continuous hq hh c)
  rw [he] at hd
  exact hd.unique (hasDerivAt_classicalHamiltonian_variation f g hf hg hpf hpg)

/-- The actual complex native H2 differential has the exact printed
physical Euler gradient, with every mass and derivative coefficient retained. -/
theorem fderiv_nativeKdV2Hamiltonian_physical (q h : ScalarSobolev 2) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (hq : ∀ n : ℤ, q.val n=periodOneCoefficient f n)
    (hh : ∀ n : ℤ, h.val n=periodOneCoefficient g n) :
    (fderiv ℂ nativeKdV2Hamiltonian q) h =
      ∫ x in (0 : ℝ)..1, g x*DifferentialPolynomial.evaluate f 0 kdv2Gradient x := by
  have hd := NLS.ComplexAnalysis.hasDerivAt_comp_affine_line nativeKdV2Hamiltonian q h
    (analyticAt_nativeKdV2Hamiltonian q).differentiableAt
  have he : (fun c : ℂ => nativeKdV2Hamiltonian (q+c • h)) =
      fun c : ℂ => classicalKdV2Hamiltonian (fun x => f x+c*g x) := by
    funext c
    exact nativeKdV2Hamiltonian_eq_of_coefficients _ _
      (hf.continuous.add (continuous_const.mul hg.continuous))
      (fun x => by rw [hpf x,hpg x]) (native_affine_physical_coefficients 2 q h f g hf.continuous hg.continuous hq hh c)
  rw [he] at hd
  exact hd.unique (hasDerivAt_classicalKdV2Hamiltonian_variation f g hf hg hpf hpg)

namespace GlobalRoughAbelianForwardData

/-- The real native source first variation is the literal restriction of
the actual complex native physical Hamiltonian differential. -/
theorem nativeSourceHierarchyHamiltonian_fderiv_eq_native (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (q h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    (fderiv ℝ (D.nativeSourceHierarchyHamiltonian m) q) h =
      (fderiv ℂ (nativeHillHierarchyHamiltonian m) q.val) h.val := by
  let J := (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))).subtypeL
  have hd := ((analyticAt_nativeHillHierarchyHamiltonian m q.val).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp q J.hasFDerivAt
  simpa only [Function.comp_def,nativeSourceHierarchyHamiltonian,ContinuousLinearMap.comp_apply] using!
    congrArg (fun L => L h) hd.fderiv

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
