import NLS.KdV.HillRoughFourierLebesgueBijection
import NLS.SequenceSpaces.DeletedSymmetricTruncation

/-! # Exact compatibility with the already-fixed global physical rough inverse

The original raw source and target embed continuously in the actual weak
spaces. Both normalization diagrams commute globally. In particular the
inverse of the stronger bijection is the restriction of the SAME global
weak inverse, with every signed raw coefficient recovered exactly.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def fourierLebesgueSourceNormalization (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p →L[ℝ] physicalRealDeletedSubmodule :=
  ((((WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))).comp
    (fourierLebesgueSourceInclusion s hs p hp h2p)).restrictScalars ℝ).comp
      (physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p).subtypeL).codRestrict _ (by
        intro a
        exact meanZeroWeightedProjection_real _ (Weight.sobolev_neg (-1)) _
          (fourierLebesgueSourceInclusion_real s hs p hp h2p a))

@[simp] theorem fourierLebesgueSourceNormalization_val (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    (fourierLebesgueSourceNormalization s hs p hp h2p a).val=
      WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
        (fourierLebesgueSourceInclusion s hs p hp h2p a.val) := rfl

def fourierLebesgueTargetNormalization (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p →L[ℝ] physicalRealDeletedSubmodule :=
  ((((WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))).comp
    (fourierLebesgueTargetInclusion s hs p hp h2p)).restrictScalars ℝ).comp
      (physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p).subtypeL).codRestrict _ (by
        intro z
        apply meanZeroWeightedProjection_real _ (Weight.sobolev_neg (-1/2))
        intro n
        change (fourierLebesgueTargetInclusion s hs p hp h2p z.val).val (-n)=
          conj ((fourierLebesgueTargetInclusion s hs p hp h2p z.val).val n)
        simpa only [fourierLebesgueTargetInclusion_apply] using z.property.1 n)

@[simp] theorem fourierLebesgueTargetNormalization_val (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    (fourierLebesgueTargetNormalization s hs p hp h2p z).val=
      WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
        (fourierLebesgueTargetInclusion s hs p hp h2p z.val) := rfl

/-- The fixed physical strong forward map commutes with the original
weak forward map on the ENTIRE native real source. -/
theorem fourierLebesgueForward_weak_commuting (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    fourierLebesgueTargetNormalization s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p a)=
      D.realWeakHomeomorph (fourierLebesgueSourceNormalization s hs p hp h2p a) := by
  have hzero : (fourierLebesgueSourceInclusion s hs p hp h2p a.val).val 0=0 := by
    simpa only [fourierLebesgueSourceInclusion_apply] using a.property.2
  have hL := WeightedCoeff.meanZeroWeightedLift_projection (Weight.sobolev (-1))
    (fourierLebesgueSourceInclusion s hs p hp h2p a.val) hzero
  apply Subtype.ext
  change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (fourierLebesgueTargetInclusion s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p a).val)=
    WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
        (fourierLebesgueSourceNormalization s hs p hp h2p a).val))
  rw [fourierLebesgueSourceNormalization_val,hL,D.fourierLebesgueForward_signed]

/-- The inverse is EXACTLY the restriction of the already-fixed global
rough inverse in its original source and target inclusion charts. -/
theorem fourierLebesgueEquiv_symm_weak_commuting (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    fourierLebesgueSourceNormalization s hs p hp h2p ((D.fourierLebesgueEquiv s hs p hp h2p).symm z)=
      D.realWeakHomeomorph.symm (fourierLebesgueTargetNormalization s hs p hp h2p z) := by
  have h := D.fourierLebesgueForward_weak_commuting s hs p hp h2p
    ((D.fourierLebesgueEquiv s hs p hp h2p).symm z)
  have hinv : D.fourierLebesgueForward s hs p hp h2p
      ((D.fourierLebesgueEquiv s hs p hp h2p).symm z)=z :=
    (D.fourierLebesgueEquiv s hs p hp h2p).apply_symm_apply z
  rw [hinv] at h
  apply D.realWeakHomeomorph.injective
  rw [D.realWeakHomeomorph.apply_symm_apply]
  exact h.symm

/-- Full signed target recovery, with the literal raw half-order shift. -/
theorem fourierLebesgueEquiv_symm_signed (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    D.signed (fourierLebesgueSourceInclusion s hs p hp h2p
      ((D.fourierLebesgueEquiv s hs p hp h2p).symm z).val)=
      fourierLebesgueTargetInclusion s hs p hp h2p z.val := by
  have h := D.fourierLebesgueForward_signed s hs p hp h2p
    ((D.fourierLebesgueEquiv s hs p hp h2p).symm z)
  have hinv : D.fourierLebesgueForward s hs p hp h2p
      ((D.fourierLebesgueEquiv s hs p hp h2p).symm z)=z :=
    (D.fourierLebesgueEquiv s hs p hp h2p).apply_symm_apply z
  rwa [hinv] at h

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
