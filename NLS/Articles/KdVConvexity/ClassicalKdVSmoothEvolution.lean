import NLS.Articles.KdVConvexity.ClassicalKdVUniqueness
import NLS.KdV.PeriodOneClassicalKdVPhysical
import NLS.KdV.PeriodOneSmoothPotential
import NLS.Articles.KdVConvexity.FourierLebesguePhaseRegularityTransfer

/-! # Arbitrary smooth initial potentials have genuine smooth physical KdV evolution

All higher original Sobolev regularities persist by compatibility of
the same physical phase evolution. Smooth synthesis and bounded H1
time differentiation give the literal PDE in the uniform physical norm.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem fourierLebesguePhaseEvolution_smooth
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hq : IsSmoothPeriodOnePotential q) (t : ℝ) :
    IsSmoothPeriodOnePotential (D.fourierLebesguePhaseEvolution B
      4 (by norm_num) 2 (by simp) (by norm_num) t q) :=
  D.fourierLebesguePhaseEvolution_preserves_all_sobolev B 4 (by norm_num) q hq t

theorem smooth_fourierLebesguePhaseEvolution_literalKdV
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hq : IsSmoothPeriodOnePotential q) (t : ℝ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      (∀ k : ℤ, (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) t q).val.val k=
        periodOneCoefficient f k) ∧
      ∃ v : C(AddCircle (2 : ℝ),ℂ),
        HasDerivAt (periodOneClassicalKdVPhysical (fun r => D.fourierLebesguePhaseEvolution B
          4 (by norm_num) 2 (by simp) (by norm_num) r q)) v t ∧
        (∀ x : ℝ, periodOneClassicalKdVPhysical (fun r => D.fourierLebesguePhaseEvolution B
          4 (by norm_num) 2 (by simp) (by norm_num) r q) t (x : AddCircle (2 : ℝ))=f x) ∧
        ∀ x : ℝ, v (x : AddCircle (2 : ℝ))=
          NLS.Articles.KdVKdV2Frequencies.kdvRHS f x := by
  obtain ⟨f,hf,hp,hc⟩ := isSmoothPeriodOnePotential_iff_exists_smooth _ |>.mp
    (D.fourierLebesguePhaseEvolution_smooth B q hq t)
  exact ⟨f,hf,hp,hc,classicalKdV_hasDerivAt_physical_of_smooth _
    (D.fourierLebesguePhaseEvolution_isClassicalKdV B q) t f hf hp hc⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
