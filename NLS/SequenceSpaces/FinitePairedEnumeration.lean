import Mathlib.Data.Multiset.Fintype
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

/-!
# Paired enumeration of finite multisets

A multiset of cardinality twice a finite index set can be assigned two values
at each index. Repeated values remain repeated; no ordering or distinctness
assumption is imposed.
-/

noncomputable section
namespace NLS

/-- Any finite multiset can be enumerated by a finite type of the same cardinality. -/
theorem exists_multiset_enumeration {α ι : Type*} [Fintype ι] (m : Multiset α)
    (h : Fintype.card ι = m.card) : ∃ f : ι → α, ∑ i, ({f i} : Multiset α) = m := by
  classical
  let e : ι ≃ m := Fintype.equivOfCardEq (h.trans (Multiset.card_coe m).symm)
  let v : m → α := fun x => (x : α)
  refine ⟨v ∘ e, ?_⟩
  have he : (Finset.univ.val.map (v ∘ e)) = m := by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    exact Multiset.map_univ_coe m
  rw [Finset.sum_eq_multiset_sum]
  calc
    _ = ((Finset.univ.val.map (v ∘ e)).map (fun a => ({a} : Multiset α))).sum := by
      rw [Multiset.map_map]
      rfl
    _ = m := by rw [Multiset.sum_map_singleton, he]

/-- A finite root multiset can be placed in two slots at each prescribed index. -/
theorem exists_paired_multiset_enumeration {α ι : Type*} [Nonempty α] (s : Finset ι) (m : Multiset α)
    (h : m.card = 2*s.card) : ∃ ξ η : ι → α, ∑ i ∈ s, ({ξ i, η i} : Multiset α) = m := by
  classical
  obtain ⟨f, hf⟩ := exists_multiset_enumeration (ι := s × Fin 2) m (by simp [h, mul_comm])
  let g (i : ι) (j : Fin 2) : α := if hi : i ∈ s then f (⟨i,hi⟩,j) else Classical.arbitrary α
  refine ⟨fun i => g i 0, fun i => g i 1, ?_⟩
  rw [Fintype.sum_prod_type] at hf
  simp only [Fin.sum_univ_two, Multiset.singleton_add] at hf
  rw [← hf]
  exact (Finset.sum_attach s (fun i => ({g i 0, g i 1} : Multiset α))).symm.trans (by
    apply Finset.sum_congr rfl
    intro i _
    simp [g, i.property])

end NLS
