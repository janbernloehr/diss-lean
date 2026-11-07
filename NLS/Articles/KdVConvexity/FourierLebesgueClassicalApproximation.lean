import NLS.Articles.KdVConvexity.ClassicalKdVSmoothEvolution
import NLS.KdV.FourierLebesgueClassicalLimitSolution

/-! # Every smooth classical approximation converges in the original native norm

The quantifier ranges over arbitrary smooth initial sequences and
arbitrary actual classical solutions. Classical uniqueness and exact
cross-space compatibility reduce the claim to the already proved
continuity of complete native trajectories. Convergence is uniform
on every compact time set, stronger than pointwise convergence.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem classicalKdV_native_inclusion_eq_phase
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hu : IsPeriodOneClassicalKdVCurve u) (t : ℝ) :
    physicalSobolevExponentInclusion h4s h2p (u t)=
      D.fourierLebesguePhaseEvolution B s hs p hp h2p t
        (physicalSobolevExponentInclusion h4s h2p (u 0)) := by
  have he := D.fourierLebesguePhaseEvolution_compatible B 4 s (by norm_num) hs 2 p
    (by simp) hp (by norm_num) h2p (u 0) (physicalSobolevExponentInclusion h4s h2p (u 0))
    (fun j => (physicalSobolevExponentInclusion_apply h4s h2p (u 0) j).symm) t
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [physicalSobolevExponentInclusion_apply,D.classicalKdV_eq_fourierLebesguePhaseEvolution B u hu t]
  exact he j

theorem tendstoUniformlyOn_arbitrary_classicalKdV_approximation
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (a : ℕ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (ha : Tendsto (fun N => physicalSobolevExponentInclusion h4s h2p (a N)) atTop (𝓝 q))
    (U : ℕ → ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hU : ∀ N, IsPeriodOneClassicalKdVCurve (U N)) (hzero : ∀ N, U N 0=a N)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N t => physicalSobolevExponentInclusion h4s h2p (U N t))
      (fun t => D.fourierLebesguePhaseEvolution B s hs p hp h2p t q) atTop K := by
  have he (N : ℕ) (t : ℝ) : physicalSobolevExponentInclusion h4s h2p (U N t)=
      D.fourierLebesguePhaseEvolution B s hs p hp h2p t
        (physicalSobolevExponentInclusion h4s h2p (a N)) := by
    rw [D.classicalKdV_native_inclusion_eq_phase B s hs h4s p hp h2p (U N) (hU N) t,hzero N]
  simp_rw [he]
  exact D.tendstoUniformlyOn_fourierLebesguePhaseEvolution B s hs p hp h2p ha K hK

theorem fourierLebesguePhaseEvolution_isClassicalLimitSolution
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    IsFourierLebesgueClassicalLimitSolution s h4s p h2p q
      (fun t => D.fourierLebesguePhaseEvolution B s hs p hp h2p t q) := by
  refine ⟨(D.fourierLebesgueTrajectoryMap B s hs p hp h2p q).continuous,
    D.fourierLebesguePhaseEvolution_zero B s hs p hp h2p q,?_⟩
  intro a _haSmooth ha U hU hzero t
  exact (D.tendstoUniformlyOn_arbitrary_classicalKdV_approximation B s hs h4s p hp h2p q a ha U hU hzero
    {t} (isCompact_singleton)).tendsto_at (mem_singleton t)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
