import NLS.SequenceSpaces.WeightedFiniteBlock
import NLS.SequenceSpaces.FourierTail

/-! # Completing a weighted tail by its finite head

Continuous coordinates and a uniform weighted tail bound give locally bounded realizations of the full sequence.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A uniform weighted tail bound and continuous raw coordinates give a
locally uniform bound for the complete sequence, including its finite head. -/
theorem exists_local_full_bound_of_tail
    {E : Type*} [TopologicalSpace E] (w : Weight) (f : E → ℤ → ℂ)
    {U : Set E} (hU : IsOpen U)
    (hc : ∀ n, ContinuousOn (fun x => f x n) U)
    (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x ∈ U, ∃ b : WeightedCoeff w p,
      (∀ n, b.val n = if K ≤ n.natAbs then f x n else 0) ∧ ‖b‖ ≤ C)
    (x₀ : E) (hx₀ : x₀ ∈ U) :
    ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ V, ∃ b : WeightedCoeff w p,
        (∀ n, b.val n = f x n) ∧ ‖b‖ ≤ B := by
  classical
  let H : E → WeightedCoeff w p := fun x => finiteBlock w (Coeff.lowFrequencies K) (f x)
  have hH : ContinuousAt H x₀ := continuousAt_finiteBlock w _ f x₀
    (fun n _ => (hc n).continuousAt (hU.mem_nhds hx₀))
  have hbound : ∀ᶠ x in 𝓝 x₀, ‖H x‖ < ‖H x₀‖+1 :=
    hH.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨V,hVsub,hV,hxV⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds hx₀) hbound)
  refine ⟨V,hV,hxV,fun x hx => (hVsub hx).1,C+‖H x₀‖+1,by positivity,?_⟩
  intro x hx
  obtain ⟨b,hb,hn⟩ := hb x (hVsub hx).1
  refine ⟨b+H x,?_,?_⟩
  · intro n
    change b.val n+(H x).val n = _
    rw [hb]
    dsimp only [H]
    rw [finiteBlock_val]
    by_cases hn : K ≤ n.natAbs
    · simp [hn,Coeff.mem_lowFrequencies,not_lt_of_ge hn]
    · simp [hn,Coeff.mem_lowFrequencies,Nat.lt_of_not_ge hn]
  · have hhead : ‖H x‖ < ‖H x₀‖+1 := (hVsub hx).2
    exact (norm_add_le b (H x)).trans (by linarith)

end NLS.WeightedCoeff
