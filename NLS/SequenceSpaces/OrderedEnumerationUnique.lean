import NLS.SequenceSpaces.OrderedFiniteEnumeration

/-!
# Uniqueness of ordered finite enumerations

Equal multisets give permuted lists. Antisymmetry forces ordered lists with
those multiplicities to agree, including at repeated entries.
-/

noncomputable section
namespace NLS

/-- The singleton sum of a finite sequence is its list multiset, with repetitions retained. -/
theorem sum_singleton_eq_coe_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (∑ i, ({f i} : Multiset α)) = (List.ofFn f : Multiset α) := by
  classical
  rw [Finset.sum_eq_multiset_sum]
  calc
    _ = ((Finset.univ.val.map f).map (fun a => ({a} : Multiset α))).sum := by
      rw [Multiset.map_map]
      rfl
    _ = _ := by rw [Multiset.sum_map_singleton, Fin.univ_val_map]

/-- Two ordered enumerations of the same multiset agree at every prescribed index. -/
theorem ordered_finset_multiset_enumeration_unique {α ι : Type*} [LinearOrder ι]
    (r : α → α → Prop) [Std.Antisymm r] (s : Finset ι) (ξ η : ι → α)
    (he : (∑ i ∈ s, ({ξ i} : Multiset α)) = ∑ i ∈ s, ({η i} : Multiset α))
    (hξ : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → r (ξ i) (ξ j))
    (hη : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → r (η i) (η j)) :
    ∀ i ∈ s, ξ i = η i := by
  classical
  let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
  have hs (f : ι → α) : (List.ofFn (fun i => f (e i)) : Multiset α) =
      ∑ i ∈ s, ({f i} : Multiset α) := by
    rw [← sum_singleton_eq_coe_ofFn]
    have hh := e.toEquiv.sum_comp (fun i : s => ({f i} : Multiset α))
    exact hh.trans (Finset.sum_attach s (fun i => ({f i} : Multiset α)))
  have hp : List.Perm (List.ofFn (fun i => ξ (e i))) (List.ofFn (fun i => η (e i))) :=
    Multiset.coe_eq_coe.mp ((hs ξ).trans (he.trans (hs η).symm))
  have hpx : (List.ofFn (fun i => ξ (e i))).Pairwise r := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hξ (e i) (e i).property (e j) (e j).property (e.monotone hij.le)
  have hpy : (List.ofFn (fun i => η (e i))).Pairwise r := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hη (e i) (e i).property (e j) (e j).property (e.monotone hij.le)
  have hl := hp.eq_of_pairwise' hpx hpy
  have hf := List.ofFn_injective hl
  intro i hi
  have h := congrFun hf (e.symm ⟨i,hi⟩)
  simpa only [OrderIso.apply_symm_apply] using h

end NLS
