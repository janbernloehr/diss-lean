import NLS.Articles.KdVConvexity.FourierLebesguePhaseEvolution
import NLS.SequenceSpaces.PhysicalRealDeletedPhaseFlow

/-! # Compatibility with the SAME globally fixed rough phase evolution

The original weak source and target Hilbert norms are retained. The
physical base actions and frequency family are literally the same as
in every stronger native Fourier-Lebesgue space.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
namespace BasePhysicalFrequencyExtension
open NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
variable (B : BasePhysicalFrequencyExtension)

def weakPhysicalFrequency (z : physicalRealDeletedSubmodule) (n : ℕ+) : ℝ :=
  (B.frequency n (weakPhysicalActions z)).re

theorem continuous_weakPhysicalFrequency (n : ℕ+) :
    Continuous (fun z => B.weakPhysicalFrequency z n) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact Complex.continuous_re.continuousAt.comp
    ((B.analytic n _ (B.contains_cone (weakPhysicalActions_nonnegative z))).continuousAt.comp
      continuous_weakPhysicalActions.continuousAt)

def weakPhysicalPhaseFlow (t : ℝ) (z : physicalRealDeletedSubmodule) : physicalRealDeletedSubmodule :=
  physicalRealDeletedPhaseFlow (signedPositiveFrequency (B.weakPhysicalFrequency z))
    (signedPositiveFrequency_neg _) t z

theorem continuous_weakPhysicalPhaseFlow :
    Continuous (fun x : ℝ × physicalRealDeletedSubmodule => B.weakPhysicalPhaseFlow x.1 x.2) :=
  continuous_physicalRealDeletedPhaseFlow_family
    (fun z => signedPositiveFrequency (B.weakPhysicalFrequency z))
    (fun _ => signedPositiveFrequency_neg _) id
    (continuous_signedPositiveFrequency _ B.continuous_weakPhysicalFrequency) continuous_id

theorem fourierLebesgueTargetNormalization_phase (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    fourierLebesgueTargetNormalization s hs p hp h2p
      (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z)=
        B.weakPhysicalPhaseFlow t
          (fourierLebesgueTargetNormalization s hs p hp h2p z) := by
  let L := fourierLebesgueTargetNormalization s hs p hp h2p
  have hfreq : B.fourierLebesguePhysicalFrequency s hs p hp h2p z=B.weakPhysicalFrequency (L z) := rfl
  apply Subtype.ext
  apply Subtype.ext
  ext j
  by_cases hj : j=0
  · subst j
    exact (L (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z)).val.property.trans
      (B.weakPhysicalPhaseFlow t (L z)).val.property.symm
  · change (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (fourierLebesgueTargetInclusion s hs p hp h2p
        (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t z).val)).val j=
      (physicalRealDeletedPhaseFlow _ _ t (L z)).val.val j
    rw [WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ j hj,
      fourierLebesgueTargetInclusion_apply,
      B.fourierLebesguePhysicalPhaseFlow_apply,physicalRealDeletedPhaseFlow_apply,hfreq]
    change (Weight.sobolev (-1/2) j : ℂ)*(Complex.exp _*z.val.val j)=
      Complex.exp _*(WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
        (fourierLebesgueTargetInclusion s hs p hp h2p z.val)).val j
    rw [WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ j hj,
      fourierLebesgueTargetInclusion_apply]
    ring

end BasePhysicalFrequencyExtension
end NLS.Articles.KdVConvexity

namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

def weakPhysicalPhaseEvolution (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (t : ℝ) (q : physicalRealDeletedSubmodule) : physicalRealDeletedSubmodule :=
  NLS.Dynamics.conjugatedEvolution D.realWeakHomeomorph B.weakPhysicalPhaseFlow t q

theorem continuous_weakPhysicalPhaseEvolution (D : GlobalRoughAbelianForwardData)
    (B : BasePhysicalFrequencyExtension) :
    Continuous (fun x : ℝ × physicalRealDeletedSubmodule => D.weakPhysicalPhaseEvolution B x.1 x.2) :=
  NLS.Dynamics.continuous_conjugatedEvolution _ _ B.continuous_weakPhysicalPhaseFlow

theorem fourierLebesguePhaseEvolution_weak_commuting (D : GlobalRoughAbelianForwardData)
    (B : BasePhysicalFrequencyExtension) (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] (t : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    fourierLebesgueSourceNormalization s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q)=
        D.weakPhysicalPhaseEvolution B t (fourierLebesgueSourceNormalization s hs p hp h2p q) := by
  change fourierLebesgueSourceNormalization s hs p hp h2p
    ((D.fourierLebesgueEquiv s hs p hp h2p).symm
      (B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p t (D.fourierLebesgueForward s hs p hp h2p q)))=_
  rw [D.fourierLebesgueEquiv_symm_weak_commuting,B.fourierLebesgueTargetNormalization_phase,
    D.fourierLebesgueForward_weak_commuting]
  rfl

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
