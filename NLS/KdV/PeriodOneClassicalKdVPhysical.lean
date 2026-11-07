import NLS.KdV.PeriodOneClassicalKdVCurve
import NLS.KdV.PeriodOneKdVNativePhysical
import NLS.Fourier.PeriodOneFourierUniqueness

/-! # Strong classical KdV curves satisfy the literal physical PDE

Bounded H1 synthesis transports the time derivative to the uniform
physical norm. At every smooth periodic representative its velocity
is exactly -u_xxx+6*u*u_x, determined by actual Fourier integrals.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier
open NLS.Articles.KdVKdV2Frequencies
open scoped ContDiff
namespace NLS.KdV

def periodOneClassicalKdVPhysical
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (t : ℝ) : C(AddCircle (2 : ℝ),ℂ) :=
  periodOneSobolevSynthesis (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4) (u t).val)

theorem classicalKdV_hasDerivAt_physical_of_smooth
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hu : IsPeriodOneClassicalKdVCurve u) (t : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ k : ℤ, (u t).val.val k=periodOneCoefficient f k) :
    ∃ v : C(AddCircle (2 : ℝ),ℂ),
      HasDerivAt (periodOneClassicalKdVPhysical u) v t ∧
      (∀ x : ℝ, periodOneClassicalKdVPhysical u t (x : AddCircle (2 : ℝ))=f x) ∧
      ∀ x : ℝ, v (x : AddCircle (2 : ℝ))=kdvRHS f x := by
  let v := periodOneSobolevSynthesis (periodOneKdVNativeVector (u t).val)
  refine ⟨v,?_,?_,?_⟩
  · exact (periodOneSobolevSynthesis.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hu.2 t)
  · have he := periodOneSobolevSynthesis_eq_of_coefficients
      (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4) (u t).val) f hf.continuous hp
      (by intro k; simpa only [WeightedCoeff.sobolevInclusion_apply] using hc k)
    exact fun x => congrFun he x
  · have hcf : ContDiff ℝ ∞ (kdvRHS f) :=
      (NLS.FunctionalAnalysis.contDiff_iteratedDeriv f hf 3).neg.add
        ((contDiff_const.mul hf).mul (NLS.FunctionalAnalysis.contDiff_iteratedDeriv f hf 1))
    have hpf : Function.Periodic (kdvRHS f) 1 := by
      intro x
      simp only [kdvRHS,NLS.FunctionalAnalysis.periodic_iteratedDeriv f 1 hp 3 x,
        NLS.FunctionalAnalysis.periodic_iteratedDeriv f 1 hp 1 x,hp x]
    have he := periodOneSobolevSynthesis_eq_of_coefficients
      (periodOneKdVNativeVector (u t).val) (kdvRHS f)
      hcf.continuous hpf
      (periodOneKdVNativeVector_coefficients (u t).val f hf hp hc)
    exact fun x => congrFun he x

end NLS.KdV
