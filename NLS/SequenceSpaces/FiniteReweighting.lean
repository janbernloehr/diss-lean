import NLS.SequenceSpaces.WeightedFiniteBlock

/-! Exact finite raw-coordinate transport between ANY two weights is
bounded linear; its operator norm controls every later analytic correction. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

def finiteReweightingCLM (w v : Weight) (S : Finset ℤ) : WeightedCoeff w p →L[ℂ] WeightedCoeff v p := by
  classical
  exact ∑ j∈S,(evalCLM w p j).smulRight (single v j 1)

theorem finiteReweightingCLM_apply (w v : Weight) (S : Finset ℤ) (A : WeightedCoeff w p) (j : ℤ) :
    (finiteReweightingCLM w v S A).val j=if j∈S then A.val j else 0 := by
  classical
  have he : finiteReweightingCLM w v S A=finiteBlock v S A.val := by
    simp only [finiteReweightingCLM,sum_apply,ContinuousLinearMap.smulRight_apply,
      evalCLM_apply,finiteBlock]
  rw [he,finiteBlock_val]

end NLS.WeightedCoeff
