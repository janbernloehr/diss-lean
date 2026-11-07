import NLS.Articles.KdVConvexity.FourierLebesgueFiniteGapApproximation
import NLS.SequenceSpaces.PhysicalRealMeanZeroPhaseAnalytic

/-! # Actual finite-support physical source orbits are native real analytic

The SAME analytic global inverse is composed with the literal finite
phase trajectory. Analyticity is in the original real source norm; no
independently chosen orbit or inverse is substituted.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity.BasePhysicalFrequencyExtension
variable (B : BasePhysicalFrequencyExtension) (s : ℝ) (hs : -1/2≤s)
  (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]

theorem analyticAt_fourierLebesguePhysicalPhaseFlow_of_finite_support
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p)
    (hf : (Function.support z.val.val).Finite) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => B.fourierLebesguePhysicalPhaseFlow s hs p hp h2p u z) t :=
  analyticAt_physicalRealMeanZeroPhaseFlow_of_finite_support _ (Weight.sobolev_neg _)
    _ _ z hf t

end NLS.Articles.KdVConvexity.BasePhysicalFrequencyExtension

namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity
variable (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
  (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]

theorem analyticAt_fourierLebesguePhaseEvolution_of_finite_support
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (hf : (Function.support (D.fourierLebesgueForward s hs p hp h2p q).val.val).Finite) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => D.fourierLebesguePhaseEvolution B s hs p hp h2p u q) t :=
  (D.fourierLebesgueEquiv_symm_analytic s hs p hp h2p _ (mem_univ _)).comp
    (B.analyticAt_fourierLebesguePhysicalPhaseFlow_of_finite_support s hs p hp h2p _ hf t)

theorem analyticAt_fourierLebesgueFiniteGapApproximation_orbit
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (N : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => D.fourierLebesguePhaseEvolution B s hs p hp h2p u
      (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N)) t := by
  apply D.analyticAt_fourierLebesguePhaseEvolution_of_finite_support B s hs p hp h2p
  rw [D.fourierLebesgueFiniteGapApproximation_coordinates]
  exact physicalRealMeanZeroWeightedTruncateExponent_finiteSupport N _

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
