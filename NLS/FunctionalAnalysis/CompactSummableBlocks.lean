import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Compactness from a strongly convergent family of finite-dimensional
approximations whose successive operator errors have summable norms. -/
noncomputable section
open Filter
namespace NLS.FunctionalAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem isCompactOperator_of_summable_blocks (B : E →L[𝕜] F)
    (P : ℕ → E →L[𝕜] E) (hP : ∀ x, Tendsto (fun j => P j x) atTop (nhds x))
    (hcompact : ∀ j, IsCompactOperator (P j))
    (hblocks : Summable (fun j => ‖B.comp (P (j+1))-B.comp (P j)‖)) :
    IsCompactOperator B := by
  have hC : CauchySeq (fun j => B.comp (P j)) := by
    apply cauchySeq_of_summable_dist
    simpa only [dist_eq_norm, norm_sub_rev] using hblocks
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hC
  have heq : L = B := by
    apply ContinuousLinearMap.ext
    intro x
    exact tendsto_nhds_unique
      (((ContinuousLinearMap.apply 𝕜 F x).continuous.tendsto L).comp hL)
      (B.continuous.tendsto x |>.comp (hP x))
  rw [heq] at hL
  exact isCompactOperator_of_tendsto hL
    (Eventually.of_forall fun j => (hcompact j).clm_comp B)

end NLS.FunctionalAnalysis
