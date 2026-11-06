import NLS.Articles.KdVConvexity.FourierLebesgueFiniteSupportSmooth
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedTruncationExponent

/-! # Native finite-gap approximation uniform on compact time intervals

The SAME global inverse is applied to literal symmetric Birkhoff
truncations. Each approximating source, and every point of its phase
orbit, has an actual smooth unit-period Fourier representative. These
are spatial smoothness conclusions; the KdV time-PDE is not assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity
variable (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1/2≤s)
  (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]

def fourierLebesgueFiniteGapApproximation
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (N : ℕ) :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p :=
  (D.fourierLebesgueEquiv s hs p hp h2p).symm
    (physicalRealMeanZeroWeightedTruncateExponent N (D.fourierLebesgueForward s hs p hp h2p q))

@[simp] theorem fourierLebesgueFiniteGapApproximation_coordinates
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (N : ℕ) :
    D.fourierLebesgueForward s hs p hp h2p (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N)=
      physicalRealMeanZeroWeightedTruncateExponent N (D.fourierLebesgueForward s hs p hp h2p q) :=
  (D.fourierLebesgueEquiv s hs p hp h2p).apply_symm_apply _

theorem tendsto_fourierLebesgueFiniteGapApproximation
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    Tendsto (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q) atTop (𝓝 q) := by
  have h := (D.fourierLebesgueHomeomorph s hs p hp h2p).symm.continuous.continuousAt.tendsto.comp
    (tendsto_physicalRealMeanZeroWeightedTruncateExponent hp (D.fourierLebesgueForward s hs p hp h2p q))
  change Tendsto (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q) atTop
    (𝓝 ((D.fourierLebesgueEquiv s hs p hp h2p).symm
      (D.fourierLebesgueForward s hs p hp h2p q))) at h
  have he : (D.fourierLebesgueEquiv s hs p hp h2p).symm
      (D.fourierLebesgueForward s hs p hp h2p q)=q :=
    (D.fourierLebesgueEquiv s hs p hp h2p).symm_apply_apply q
  rw [he] at h
  exact h

theorem fourierLebesgueFiniteGapApproximation_smooth
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (N : ℕ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ ∀ n : ℤ,
      (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N).val.val n=periodOneCoefficient f n :=
  D.exists_smooth_fourierLebesgue_inverse_of_finite_support s hs p hp h2p _
    (physicalRealMeanZeroWeightedTruncateExponent_finiteSupport N _)

theorem fourierLebesgueFiniteGapApproximation_orbit_smooth
    (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (N : ℕ) (t : ℝ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ ∀ n : ℤ,
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p t
        (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N)).val.val n=periodOneCoefficient f n := by
  let u := D.fourierLebesguePhaseEvolution B s hs p hp h2p t
    (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N)
  have hf : (Function.support (D.fourierLebesgueForward s hs p hp h2p u).val.val).Finite := by
    rw [D.fourierLebesguePhaseEvolution_coordinates,D.fourierLebesgueFiniteGapApproximation_coordinates,
      B.fourierLebesguePhysicalPhaseFlow_support]
    exact physicalRealMeanZeroWeightedTruncateExponent_finiteSupport N _
  have h := D.exists_smooth_fourierLebesgue_inverse_of_finite_support s hs p hp h2p
    (D.fourierLebesgueForward s hs p hp h2p u) hf
  have he : (D.fourierLebesgueEquiv s hs p hp h2p).symm
      (D.fourierLebesgueForward s hs p hp h2p u)=u :=
    (D.fourierLebesgueEquiv s hs p hp h2p).symm_apply_apply u
  rwa [he] at h

/-- Literal symmetric Birkhoff approximations converge in the ORIGINAL
source norm, uniformly over every compact real time set. -/
theorem tendstoUniformlyOn_fourierLebesgueFiniteGapApproximation
    (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N t => D.fourierLebesguePhaseEvolution B s hs p hp h2p t
      (D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N))
      (fun t => D.fourierLebesguePhaseEvolution B s hs p hp h2p t q) atTop K :=
  D.tendstoUniformlyOn_fourierLebesguePhaseEvolution B s hs p hp h2p
    (D.tendsto_fourierLebesgueFiniteGapApproximation s hs p hp h2p q) K hK

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
