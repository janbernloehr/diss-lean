import NLS.Articles.KdVConvexity.FourierLebesgueFinitePhaseHamiltonian
import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapModeOpening

/-! # Every actual finite phase orbit has its physical native finite-gap source

Native H1 membership and spectral finite-gap collapse are conclusions,
proved from the SAME actual raw signed Birkhoff coordinates. They are
not additional regularity or spectral hypotheses on the orbit.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity
variable (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
  (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]

theorem exists_native_H1_at_finitePhaseEvolution
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (hf : (Function.support (D.fourierLebesgueForward s hs p hp h2p q).val.val).Finite) (t : ℝ) :
    ∃ a : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)),
      nativeHillSource 1 a.val=fourierLebesgueSourceInclusion s hs p hp h2p
        (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val := by
  let u := D.fourierLebesguePhaseEvolution B s hs p hp h2p t q
  have hfu : (Function.support (D.fourierLebesgueForward s hs p hp h2p u).val.val).Finite := by
    change (Function.support (D.fourierLebesgueForward s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q)).val.val).Finite
    rw [D.fourierLebesguePhaseEvolution_coordinates,B.fourierLebesguePhysicalPhaseFlow_support]
    exact hf
  have hfin := D.positive_finiteSupport_of_fourierLebesgue_target s hs p hp h2p
    (D.fourierLebesgueForward s hs p hp h2p u) hfu
  have he : (D.fourierLebesgueEquiv s hs p hp h2p).symm
      (D.fourierLebesgueForward s hs p hp h2p u)=u :=
    (D.fourierLebesgueEquiv s hs p hp h2p).symm_apply_apply u
  rw [he] at hfin
  exact exists_native_of_finite_positive_support D _
    (fourierLebesgueSourceInclusion_real s hs p hp h2p u)
    (by simpa only [fourierLebesgueSourceInclusion_apply] using u.property.2) hfin 1

theorem native_H1_at_finitePhaseEvolution_closed_outside (t : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (a : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (ha : nativeHillSource 1 a.val=fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val)
    (S : Finset ℕ+)
    (hS : ∀ n : ℕ+, n∉S → (D.fourierLebesgueForward s hs p hp h2p q).val.val (n : ℤ)=0) :
    ∀ n : ℕ+, n∉S → hillRealGapHalfLength (nativeHillPhysicalSource 1 a.val a.property.1).val
      (nativeHillPhysicalSource 1 a.val a.property.1).property.1
      (nativeHillPhysicalSource 1 a.val a.property.1).property.2 n=0 := by
  intro n hn
  apply (D.rawIntegerForwardHomeomorph_zero_iff_closed 1 a n).mp
  have he := congrArg (fun z => z.val (n : ℤ)) (D.rawIntegerForwardHomeomorph_signed 1 a)
  rw [WeightedCoeff.sobolevInclusion_apply,ha] at he
  rw [he]
  exact D.fourierLebesguePhaseEvolution_component_zero_outside B s hs p hp h2p t q S hS true n hn

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
