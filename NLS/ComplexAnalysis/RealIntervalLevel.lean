import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Choosing a real square-root level continuously on an interval
A continuous function whose square stays above a positive squared level
cannot switch from the positive branch to the negative branch.
-/

open Set
namespace NLS.ComplexAnalysis

/-- A continuous function with a positive initial level and no values in the middle strip stays above that level. -/
theorem level_le_on_Icc_of_sq_ge (f : ℝ → ℝ) {a b L : ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Icc a b)) (ha : L ≤ f a)
    (hs : ∀ x ∈ Icc a b, L^2 ≤ (f x)^2) : ∀ x ∈ Icc a b, L ≤ f x := by
  intro x hx
  have hnonneg : 0 ≤ f x := by
    by_contra hn
    have hneg : f x < 0 := lt_of_not_ge hn
    obtain ⟨y,hy,he⟩ := intermediate_value_Icc' hx.1
      (hf.mono (Icc_subset_Icc le_rfl hx.2)) (show 0 ∈ Icc (f x) (f a) from ⟨hneg.le,by linarith⟩)
    have hs' := hs y ⟨hy.1,hy.2.trans hx.2⟩
    rw [he] at hs'
    nlinarith
  have hs' := hs x hx
  nlinarith

end NLS.ComplexAnalysis
