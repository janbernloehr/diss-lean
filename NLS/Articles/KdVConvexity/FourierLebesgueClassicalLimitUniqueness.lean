import NLS.Articles.KdVConvexity.FourierLebesgueSmoothDensity

/-! # Existence and uniqueness in the universal classical-limit solution class

Every candidate solution is tested against genuine smooth classical KdV
solutions from a dense sequence of smooth data. Its pointwise limits
agree with the same continuous global native phase evolution.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem classicalLimitSolution_eq_fourierLebesguePhaseEvolution
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (γ : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (hγ : IsFourierLebesgueClassicalLimitSolution s h4s p h2p q γ) :
    γ=(fun t => D.fourierLebesguePhaseEvolution B s hs p hp h2p t q) := by
  obtain ⟨a,ha,hconv⟩ := D.exists_smooth_H4_approximation s hs h4s p hp h2p q
  let U (N : ℕ) (t : ℝ) := D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) t (a N)
  have hU (N : ℕ) : IsPeriodOneClassicalKdVCurve (U N) := D.fourierLebesguePhaseEvolution_isClassicalKdV B (a N)
  have hzero (N : ℕ) : U N 0=a N := D.fourierLebesguePhaseEvolution_zero B 4 (by norm_num) 2 (by simp) (by norm_num) _
  have hactual := D.fourierLebesguePhaseEvolution_isClassicalLimitSolution B s hs h4s p hp h2p q
  funext t
  exact tendsto_nhds_unique (hγ.2.2 a ha hconv U hU hzero t)
    (hactual.2.2 a ha hconv U hU hzero t)

theorem existsUnique_fourierLebesgueClassicalLimitSolution
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    ∃! γ : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p,
      IsFourierLebesgueClassicalLimitSolution s h4s p h2p q γ :=
  ⟨_,D.fourierLebesguePhaseEvolution_isClassicalLimitSolution B s hs h4s p hp h2p q,
    fun γ hγ => D.classicalLimitSolution_eq_fourierLebesguePhaseEvolution B s hs h4s p hp h2p q γ hγ⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
