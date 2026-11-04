import Mathlib.Topology.Sequences
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

/-! For a naturally indexed family in a metric space, a property holds
on its closure if it holds at every family point and at every escaping
sequence limit. Repeated bounded indices and escaping indices are both
covered without assuming the property itself is closed. -/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis

theorem property_on_closure_range_of_escaping_limits
    {X : Type*} [MetricSpace X] (F : ℕ → X) (P : X → Prop)
    (hF : ∀ k, P (F k))
    (hescape : ∀ n : ℕ → ℕ, Tendsto n atTop atTop → ∀ x : X,
      Tendsto (fun j => F (n j)) atTop (𝓝 x) → P x)
    (x : X) (hx : x ∈ closure (range F)) : P x := by
  obtain ⟨u,hu,hlim⟩ := mem_closure_iff_seq_limit.mp hx
  choose n hn using hu
  have ht : Tendsto (fun j => F (n j)) atTop (𝓝 x) :=
    hlim.congr' (Eventually.of_forall (fun j => (hn j).symm))
  by_cases hrepeat : ∃ k : ℕ, ∃ᶠ j in atTop, n j = k
  · obtain ⟨k,hk⟩ := hrepeat
    have he : x = F k := tendsto_nhds_unique_of_frequently_eq ht tendsto_const_nhds
      (hk.mono (fun j hj => congrArg F hj))
    rw [he]
    exact hF k
  · have hnat : Tendsto n atTop atTop := by
      apply tendsto_atTop.mpr
      intro N
      have he : ∀ᶠ j in atTop, ∀ k ∈ Finset.range N, n j ≠ k := by
        rw [Finset.eventually_all]
        intro k _
        apply not_frequently.mp
        intro hk
        exact hrepeat ⟨k,hk⟩
      filter_upwards [he] with j hj
      by_contra h
      exact hj (n j) (Finset.mem_range.mpr (by omega)) rfl
    exact hescape n hnat x ht

end NLS.FunctionalAnalysis
