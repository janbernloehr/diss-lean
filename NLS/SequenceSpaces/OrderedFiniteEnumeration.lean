import NLS.SequenceSpaces.FiniteEnumeration
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise

/-!
# Ordered enumeration of a finite multiset

Sorting retains repeated values. The order is supplied as a relation, so
complex lexicographic order need not replace any ambient numeric order.
-/

noncomputable section
namespace NLS

/-- Enumerate a multiset in increasing order on a prescribed finite ordered index set. -/
theorem exists_ordered_finset_multiset_enumeration {α ι : Type*} [Nonempty α] [LinearOrder ι]
    (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] [Std.Refl r]
    (s : Finset ι) (m : Multiset α) (h : m.card = s.card) :
    ∃ ξ : ι → α, (∑ i ∈ s, ({ξ i} : Multiset α)) = m ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≤ j → r (ξ i) (ξ j) := by
  classical
  let l := m.sort r
  let e : Fin l.length ≃o s := s.orderIsoOfFin (by simp [l, h])
  let f : s → α := fun i => l.get (e.symm i)
  let ξ : ι → α := fun i => if hi : i ∈ s then f ⟨i,hi⟩ else Classical.arbitrary α
  have hf : (∑ i : s, ({f i} : Multiset α)) = m := by
    rw [← e.toEquiv.sum_comp]
    change (∑ i : Fin l.length, ({l.get (e.symm (e i))} : Multiset α)) = m
    simp only [OrderIso.symm_apply_apply]
    rw [← List.sum_ofFn]
    change (List.ofFn ((fun a : α => ({a} : Multiset α)) ∘ l.get)).sum = m
    rw [← List.map_ofFn, List.ofFn_get]
    change ((l : Multiset α).map (fun a => ({a} : Multiset α))).sum = m
    rw [Multiset.sum_map_singleton]
    exact Multiset.sort_eq m r
  refine ⟨ξ, ?_, ?_⟩
  · rw [← hf]
    exact (Finset.sum_attach s (fun i => ({ξ i} : Multiset α))).symm.trans (by
      apply Finset.sum_congr rfl
      intro i _
      simp only [ξ, dif_pos i.property])
  · intro i hi j hj hij
    simp only [ξ, dif_pos hi, dif_pos hj, f]
    exact (Multiset.pairwise_sort m r).rel_get_of_le (e.symm.monotone hij)

end NLS
