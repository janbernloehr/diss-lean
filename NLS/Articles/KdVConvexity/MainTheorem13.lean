import NLS.Articles.KdVConvexity.FourierLebesgueClassicalLimitUniqueness
import NLS.Articles.KdVConvexity.WeakPhysicalClassicalLimit
import NLS.Articles.KdVConvexity.MainTheorem13Preparation

/-! # Theorem 1.3: global C0 well-posedness in the original Fourier-Lebesgue spaces

One actual physical map and frequency extension precede every order
-1/2 <= s <= 0 and finite exponent p >= 2. The same evolution gives the
unique solution in the universal smooth classical-approximation sense.
Initial data depend continuously in C(R,X), the compact-open topology.
The original weak Hminus1 normalization commutes at every real time.
Actual classical KdV recovery and uniqueness are proved independently
from the literal native conservative differential equation.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

structure Theorem13PhysicalData where
  physicalMap : GlobalRoughAbelianForwardData
  physicalFrequencies : BasePhysicalFrequencyExtension
  classicalKdV : ∀ q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2,
    IsPeriodOneClassicalKdVCurve (fun t => physicalMap.fourierLebesguePhaseEvolution physicalFrequencies
      4 (by norm_num) 2 (by simp) (by norm_num) t q)
  classical_unique : ∀ u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2,
    IsPeriodOneClassicalKdVCurve u → ∀ t : ℝ,
      u t=physicalMap.fourierLebesguePhaseEvolution physicalFrequencies
        4 (by norm_num) 2 (by simp) (by norm_num) t (u 0)
  native_wellposed : ∀ (s : ℝ) (_hs : -1/2≤s) (hupper : s≤0),
    ∀ (p : ℝ≥0∞) (_hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
    ∀ q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p,
      ∃! γ : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p,
        IsFourierLebesgueClassicalLimitSolution s (by linarith) p h2p q γ
  native_solution : ∀ (s : ℝ) (hs : -1/2≤s) (hupper : s≤0),
    ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
    ∀ q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p,
      IsFourierLebesgueClassicalLimitSolution s (by linarith) p h2p q
        (fun t => physicalMap.fourierLebesguePhaseEvolution physicalFrequencies s hs p hp h2p t q)
  continuous_complete_trajectories : ∀ (s : ℝ) (hs : -1/2≤s), s≤0 →
    ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
      Continuous (fun q => physicalMap.fourierLebesgueTrajectoryMap physicalFrequencies s hs p hp h2p q)
  weak_recovery : ∀ (s : ℝ) (hs : -1/2≤s), s≤0 →
    ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)], ∀ t q,
      fourierLebesgueSourceNormalization s hs p hp h2p
        (physicalMap.fourierLebesguePhaseEvolution physicalFrequencies s hs p hp h2p t q)=
      physicalMap.weakPhysicalPhaseEvolution physicalFrequencies t
        (fourierLebesgueSourceNormalization s hs p hp h2p q)

/-- Global C0 well-posedness in precisely the source's full native range,
with universal classical-limit solutions and the SAME physical weak flow. -/
theorem theorem_1_3 : Nonempty Theorem13PhysicalData := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  obtain ⟨B⟩ := nonempty_basePhysicalFrequencyExtension
  refine ⟨⟨D,B,D.fourierLebesguePhaseEvolution_isClassicalKdV B,
    D.classicalKdV_eq_fourierLebesguePhaseEvolution B,?_,?_,?_,?_⟩⟩
  · intro s hs hupper p hp h2p inst q
    exact D.existsUnique_fourierLebesgueClassicalLimitSolution B s hs (by linarith) p hp h2p q
  · intro s hs hupper p hp h2p inst q
    exact D.fourierLebesguePhaseEvolution_isClassicalLimitSolution B s hs (by linarith) p hp h2p q
  · intro s hs _hupper p hp h2p inst
    exact (D.fourierLebesgueTrajectoryMap B s hs p hp h2p).continuous
  · intro s hs _hupper p hp h2p inst t q
    exact D.fourierLebesguePhaseEvolution_weak_commuting B s hs p hp h2p t q

end NLS.Articles.KdVConvexity
