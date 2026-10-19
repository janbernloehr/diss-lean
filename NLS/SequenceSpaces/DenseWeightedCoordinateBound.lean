import NLS.SequenceSpaces.WeightedCoefficientLimit

/-! # Extending a weighted bound from a dense source set

Continuous raw coordinates extend a uniform weighted bound from a dense subset of an open set to the whole set.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- A uniform weighted bound on a dense subset of an open set extends to
every point when the individual raw coordinates are continuous. -/
theorem exists_of_dense_bounded_coordinates
    {E : Type*} [TopologicalSpace E] [FrechetUrysohnSpace E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : Weight) (S U : Set E)
    (hS : Dense S) (hU : IsOpen U) (f : E → ℤ → ℂ)
    (hc : ∀ n, ContinuousOn (fun x => f x n) U) (C : ℝ)
    (hb : ∀ x ∈ U, x ∈ S → ∃ a : WeightedCoeff w p, (∀ n, a.val n = f x n) ∧ ‖a‖ ≤ C)
    (x : E) (hx : x ∈ U) :
    ∃ a : WeightedCoeff w p, (∀ n, a.val n = f x n) ∧ ‖a‖ ≤ C := by
  classical
  obtain ⟨y,hy,ht⟩ := mem_closure_iff_seq_limit.mp (hS.open_subset_closure_inter hU hx)
  choose a ha han using fun i => hb (y i) (hy i).1 (hy i).2
  apply exists_of_bounded_coefficientwise_tendsto (l := atTop) w a (f x) C han
  intro n
  simp_rw [ha]
  exact ((hc n).continuousAt (hU.mem_nhds hx)).tendsto.comp ht

end NLS.WeightedCoeff
