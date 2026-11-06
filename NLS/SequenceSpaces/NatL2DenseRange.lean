import Mathlib.Analysis.Normed.Lp.lpSpace

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.SequenceSpaces

/-- Attaining every complex single makes a real bounded linear map have
dense range in the full complex sequence Hilbert space. -/
theorem denseRange_natL2_of_single_preimages
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] lp (fun _ : ℕ => ℂ) 2)
    (h : ∀ (k : ℕ) (z : ℂ), ∃ x : E, T x = lp.single 2 k z) : DenseRange T := by
  intro z
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z)
  apply Eventually.of_forall
  intro s
  exact T.toLinearMap.range.sum_mem (fun k _ => h k (z k))

end NLS.SequenceSpaces
