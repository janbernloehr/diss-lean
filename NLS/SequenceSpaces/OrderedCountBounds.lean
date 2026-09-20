import Mathlib.Data.Finset.Card
import Mathlib.Order.Monotone.Basic

/-!
# Recovering ordered coordinate bounds from counts

A subset with at least as many entries as the prefix through an index
forces an upper bound at that index. The dual statement uses a suffix.
-/

open scoped Classical
namespace NLS

/-- A lower bound on the size of a bounded subset controls an ordered entry from above. -/
theorem le_of_prefix_card_le {ι α : Type*} [LinearOrder ι] [LinearOrder α]
    (s t : Finset ι) (f : ι → α) (hf : MonotoneOn f (s : Set ι))
    (i : ι) (hi : i ∈ s) (a : α) (ht : t ⊆ s) (hb : ∀ j ∈ t, f j ≤ a)
    (hc : (s.filter (fun j => j ≤ i)).card ≤ t.card) : f i ≤ a := by
  by_contra hn
  have hai : a < f i := lt_of_not_ge hn
  have hs : t ⊂ s.filter (fun j => j ≤ i) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_,?_⟩
    · intro j hj
      refine Finset.mem_filter.mpr ⟨ht hj,?_⟩
      by_contra hji
      exact (hai.trans_le (hf hi (ht hj) (le_of_not_ge hji))).not_ge (hb j hj)
    · intro he
      have hit : i ∈ t := he ▸ Finset.mem_filter.mpr ⟨hi,le_rfl⟩
      exact hai.not_ge (hb i hit)
  exact (Finset.card_lt_card hs).not_ge hc

/-- The suffix version controls an ordered entry from below. -/
theorem le_of_suffix_card_le {ι α : Type*} [LinearOrder ι] [LinearOrder α]
    (s t : Finset ι) (f : ι → α) (hf : MonotoneOn f (s : Set ι))
    (i : ι) (hi : i ∈ s) (a : α) (ht : t ⊆ s) (hb : ∀ j ∈ t, a ≤ f j)
    (hc : (s.filter (fun j => i ≤ j)).card ≤ t.card) : a ≤ f i :=
  le_of_prefix_card_le (ι := ιᵒᵈ) (α := αᵒᵈ) s t f
    (fun _ hx _ hy h => hf hy hx h) i hi a ht hb hc

end NLS
