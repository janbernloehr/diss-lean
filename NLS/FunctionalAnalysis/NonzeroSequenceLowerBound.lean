import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Instances.Nat

/-! A sequence with no zero term and a nonzero norm limit is bounded
away from zero. The finite head is retained explicitly. -/
noncomputable section
open Set Filter Topology
open scoped Classical
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E]

theorem exists_positive_lower_norm_on_finset {ι : Type*} (f : ι → E) (s : Finset ι)
    (hf : ∀ i ∈ s, f i ≠ 0) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ ‖f i‖ := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ,hδ,hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min δ ‖f i‖,lt_min hδ (norm_pos_iff.mpr (hf i (Finset.mem_insert_self _ _))),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound j hjs)

theorem exists_positive_lower_norm_of_tendsto (f : ℕ → E) (a : E)
    (ha : a ≠ 0) (hf : ∀ j, f j ≠ 0) (ht : Tendsto f atTop (𝓝 a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j, δ ≤ ‖f j‖ := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (‖a‖/2) (half_pos ha')
  obtain ⟨δ,hδ,hhead⟩ := exists_positive_lower_norm_on_finset f (Finset.range N) (fun j _ => hf j)
  refine ⟨min (‖a‖/2) δ,lt_min (half_pos ha') hδ,?_⟩
  intro j
  by_cases hj : N ≤ j
  · apply (min_le_left _ _).trans
    have hdist := hN j hj
    rw [dist_eq_norm] at hdist
    have htri : ‖a‖ ≤ ‖f j-a‖+‖f j‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_sub_add a (f j)
    linarith
  · exact (min_le_right _ _).trans (hhead j (Finset.mem_range.mpr (by omega)))

end NLS.FunctionalAnalysis
