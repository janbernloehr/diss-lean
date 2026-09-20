import NLS.SequenceSpaces.FinitePairedEnumeration

/-!
# Single-slot enumeration of a finite multiset

A prescribed finite index set can label a multiset of the same cardinality,
retaining repeated entries.
-/

noncomputable section
namespace NLS

/-- Enumerate a multiset on a finite set of indices, with arbitrary values elsewhere. -/
theorem exists_finset_multiset_enumeration {α ι : Type*} [Nonempty α] (s : Finset ι)
    (m : Multiset α) (h : m.card = s.card) :
    ∃ ξ : ι → α, ∑ i ∈ s, ({ξ i} : Multiset α) = m := by
  classical
  obtain ⟨f, hf⟩ := exists_multiset_enumeration (ι := s) m (by simpa using h.symm)
  let g (i : ι) : α := if hi : i ∈ s then f ⟨i,hi⟩ else Classical.arbitrary α
  refine ⟨g, ?_⟩
  rw [← hf]
  exact (Finset.sum_attach s (fun i => ({g i} : Multiset α))).symm.trans (by
    apply Finset.sum_congr rfl
    intro i _
    simp [g, i.property])

end NLS
