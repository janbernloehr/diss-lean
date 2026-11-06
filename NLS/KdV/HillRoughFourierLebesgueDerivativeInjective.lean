import NLS.ComplexAnalysis.DerivativeInjectiveRestriction
import NLS.SequenceSpaces.MeanZeroWeightedProjectionInjective
import NLS.KdV.HillRoughFourierLebesgueForwardAllExponents

/-! # Injectivity of the actual native Fourier-Lebesgue Birkhoff derivative

The global fixed weak diagram and already-proved weak analytic inverse
identify the derivatives. No new inverse, Fourier principal or closed-gap
exception is assumed. Both original normalization maps are injections.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem fourierLebesgueSourceNormalization_injective
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Function.Injective (fourierLebesgueSourceNormalization s hs p hp h2p) := by
  intro a b hab
  have he := congrArg Subtype.val hab
  rw [fourierLebesgueSourceNormalization_val,fourierLebesgueSourceNormalization_val] at he
  have hq := WeightedCoeff.meanZeroWeightedProjection_injective_of_zero _ _ _
    (by simpa only [fourierLebesgueSourceInclusion_apply] using a.property.2)
    (by simpa only [fourierLebesgueSourceInclusion_apply] using b.property.2) he
  apply Subtype.ext
  apply Subtype.ext
  funext n
  simpa only [fourierLebesgueSourceInclusion_apply] using congrArg (fun q => q.val n) hq

theorem fourierLebesgueTargetNormalization_injective
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Function.Injective (fourierLebesgueTargetNormalization s hs p hp h2p) := by
  intro a b hab
  have he := congrArg Subtype.val hab
  rw [fourierLebesgueTargetNormalization_val,fourierLebesgueTargetNormalization_val] at he
  have hq := WeightedCoeff.meanZeroWeightedProjection_injective_of_zero _ _ _
    (by simpa only [fourierLebesgueTargetInclusion_apply] using a.property.2)
    (by simpa only [fourierLebesgueTargetInclusion_apply] using b.property.2) he
  apply Subtype.ext
  apply Subtype.ext
  funext n
  simpa only [fourierLebesgueTargetInclusion_apply] using congrArg (fun q => q.val n) hq

/-- At EVERY native real source the ACTUAL derivative is injective,
for every finite p>=2 and every s>=-1/2, including all closed gaps. -/
theorem fourierLebesgueForward_fderiv_injective (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    Function.Injective (fderiv ℝ (D.fourierLebesgueForward s hs p hp h2p) a) := by
  let L := fourierLebesgueSourceNormalization s hs p hp h2p
  have hweak : DifferentiableAt ℝ D.realWeakHomeomorph (L a) :=
    (D.realWeakForward_analytic (L a) (mem_univ _)).differentiableAt
  have hinverse : DifferentiableAt ℝ D.realWeakHomeomorph.symm (D.realWeakHomeomorph (L a)) :=
    (D.realWeakEquiv_symm_analytic _ (mem_univ _)).differentiableAt
  have hweakInj := NLS.ComplexAnalysis.fderiv_injective_of_differentiable_leftInverse
    D.realWeakHomeomorph D.realWeakHomeomorph.symm (L a) hweak hinverse
    D.realWeakHomeomorph.symm_apply_apply
  exact NLS.ComplexAnalysis.fderiv_injective_of_linear_intertwining
    (D.fourierLebesgueForward s hs p hp h2p) D.realWeakHomeomorph L
    (fourierLebesgueTargetNormalization s hs p hp h2p) a
    (D.fourierLebesgueForward_analytic s hs p hp h2p a (mem_univ _)).differentiableAt hweak
    (D.fourierLebesgueForward_weak_commuting s hs p hp h2p)
    (fourierLebesgueSourceNormalization_injective s hs p hp h2p) hweakInj

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
