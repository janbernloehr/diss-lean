import NLS.KdV.HillRoughFourierLebesgueInverseAllExponents

/-! # The actual native real Fourier-Lebesgue homeomorphism -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def fourierLebesgueHomeomorph (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p ≃ₜ
      physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p where
  toEquiv := D.fourierLebesgueEquiv s hs p hp h2p
  continuous_toFun := continuous_iff_continuousAt.mpr (fun a =>
    (D.fourierLebesgueForward_analytic s hs p hp h2p a (mem_univ _)).continuousAt)
  continuous_invFun := continuous_iff_continuousAt.mpr (fun z =>
    (D.fourierLebesgueEquiv_symm_analytic s hs p hp h2p z (mem_univ _)).continuousAt)

@[simp] theorem fourierLebesgueHomeomorph_apply (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    D.fourierLebesgueHomeomorph s hs p hp h2p q=D.fourierLebesgueForward s hs p hp h2p q := rfl

@[simp] theorem fourierLebesgueHomeomorph_symm_apply (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    (D.fourierLebesgueHomeomorph s hs p hp h2p).symm z=
      (D.fourierLebesgueEquiv s hs p hp h2p).symm z := rfl

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
