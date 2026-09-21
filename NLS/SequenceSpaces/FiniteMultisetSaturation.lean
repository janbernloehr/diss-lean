import NLS.SequenceSpaces.OrderedEnumerationUnique

/-!
# Exhausting a root multiset by distinct witnesses

An injective family of entries in a multiset already exhausts the entire
multiset when its finite index set has the same cardinality. No extra
entries or repeated occurrences can remain.
-/

noncomputable section
namespace NLS

/-- A finite singleton sum is the mapped index multiset. -/
theorem sum_singleton_eq_multiset_map {ι α : Type*} (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, ({f i} : Multiset α)) = s.val.map f := by
  rw [Finset.sum_eq_multiset_sum]
  calc
    _ = ((s.val.map f).map (fun a => ({a} : Multiset α))).sum := by rw [Multiset.map_map]; rfl
    _ = _ := Multiset.sum_map_singleton _

/-- Distinct witnesses exhaust a multiset when their number equals its total multiplicity. -/
theorem sum_singleton_eq_of_injective_mem_card {ι α : Type*} (s : Finset ι) (f : ι → α)
    (m : Multiset α) (hf : Function.Injective f) (hm : ∀ i ∈ s, f i ∈ m)
    (hc : m.card = s.card) : (∑ i ∈ s, ({f i} : Multiset α)) = m := by
  rw [sum_singleton_eq_multiset_map]
  apply Multiset.eq_of_le_of_card_le
  · apply (Multiset.le_iff_subset (Multiset.Nodup.map hf s.nodup)).mpr
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hz
    exact hm i hi
  · rw [Multiset.card_map]
    exact hc.le

end NLS
