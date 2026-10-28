import NLS.ZakharovShabat.SourceDiagonalSmallBound
import NLS.ZakharovShabat.SourceCubicMovingCoefficient

/-! # Small-amplitude diagonal bounds for the original family

Supporting estimates for the unresolved final weighted gap sum on p.44.
The actual counted-root gap still needs comparison with the coefficient sum.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceCubicSmallDiagonalFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- A fixed quadratic-amplitude majorant for the three-mode family. -/
def sourceCubicDiagonalBound (n : ℤ) : ℝ :=
  sourceDiagonalNormConstant (p := 4) (by simp)*(sourceCubicTailNormBound n)^2

/-- The original family diagonal is bounded by the quadratic amplitude on every full strip. -/
theorem sourceCubicDiagonal_norm_le (n m : ℤ) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hsmall : SourceCubicSmall n s) (z : ℂ) (hz : z ∈ resonantStrip m) :
    ‖sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) m z‖ ≤ sourceCubicDiagonalBound n*s^2 := by
  have hh : ‖weightedPotentialSquareInShift (by simp) SpectralWeight.one
      (unitWeightedPairEquiv (sourceCubicTailFamily n s)) m z hz‖ ≤ 1/2 := by
    rw [unitWeightedPairEquiv_sourceCubicTailFamily]
    exact (resonantCubic_square_bound (by simp) SpectralWeight.one _ m z hz).trans hsmall
  apply (norm_sourceResonantA_le_norm_sq (by simp) (sourceCubicTailFamily n s) m z hz hh).trans
  have hb := pow_le_pow_left₀ (norm_nonneg _) (sourceCubicTailFamily_norm_le n s hs hs1) 2
  exact (mul_le_mul_of_nonneg_left hb (sourceDiagonalNormConstant_nonneg (p := 4) (by simp))).trans_eq (by
    unfold sourceCubicDiagonalBound
    ring)

/-- The original family diagonal is analytic on a neighborhood of the entire strip under global smallness. -/
theorem sourceCubicDiagonal_analytic (n m : ℤ) (s : ℝ) (hsmall : SourceCubicSmall n s) :
    AnalyticOnNhd ℂ (sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) m) (resonantStrip m) := by
  intro z hz
  have hh : ‖weightedPotentialSquareInShift (by simp) SpectralWeight.one
      (unitWeightedPairEquiv (sourceCubicTailFamily n s)) m z hz‖ < 1 := by
    rw [unitWeightedPairEquiv_sourceCubicTailFamily]
    exact ((resonantCubic_square_bound (by simp) SpectralWeight.one _ m z hz).trans hsmall).trans_lt (by norm_num)
  exact (analyticAt_sourceCorrectionEntryFunction (by simp) (sourceCubicTailFamily n s) m z hz hh 0 0).comp
    (analyticAt_const.prod analyticAt_id)

/-- Its derivative has a quadratic-amplitude bound throughout every refined disk. -/
theorem sourceCubicDiagonal_deriv_le (n m : ℤ) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hsmall : SourceCubicSmall n s) (x : ℂ) (hx : x ∈ refinedResonantDisk m) :
    ‖deriv (sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) m) x‖ ≤
      (sourceCubicDiagonalBound n/(Real.pi/4))*s^2 := by
  have h := norm_deriv_le_on_refined_disk_of_bound m _ _ (sourceCubicDiagonal_analytic n m s hsmall)
    (sourceCubicDiagonal_norm_le n m s hs hs1 hsmall) x hx
  exact h.trans_eq (by ring)

/-- Unit weighting identifies the entire original diagonal function. -/
theorem sourceCubicDiagonal_eq (n m : ℤ) (s : ℝ) :
    sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) m =
      weightedResonantAExtension (by simp) SpectralWeight.one (weightedCubicTailFamily n s) m := by
  funext z
  simp only [sourceResonantAFunction,sourceCorrectionEntryFunction,
    unitWeightedPairEquiv_sourceCubicTailFamily,weightedResonantAExtension]

end NLS.ZakharovShabat
