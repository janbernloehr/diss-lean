import NLS.SequenceSpaces.OrderedFiniteEnumeration
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered paired enumeration of a multiset

Sorting two slots per index keeps all repetitions and orders both the
slots at one index and the last slot before the next index's first slot.
-/

noncomputable section
namespace NLS

/-- Enumerate a multiset in ordered pairs on any finite linearly ordered index set. -/
theorem exists_ordered_paired_multiset_enumeration {α ι : Type*} [Nonempty α] [LinearOrder ι]
    (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] [Std.Refl r]
    (s : Finset ι) (m : Multiset α) (h : m.card = 2*s.card) :
    ∃ ξ η : ι → α, (∑ i ∈ s, ({ξ i,η i} : Multiset α)) = m ∧
      (∀ i ∈ s, r (ξ i) (η i)) ∧ ∀ i ∈ s, ∀ j ∈ s, i < j → r (η i) (ξ j) := by
  classical
  let t : Finset (ι ×ₗ Fin 2) := (s ×ˢ Finset.univ).map toLex.toEmbedding
  obtain ⟨f,hf,hs⟩ := exists_ordered_finset_multiset_enumeration r t m (by simp [t,h,mul_comm])
  have ht (i : ι) (hi : i ∈ s) (j : Fin 2) : toLex (i,j) ∈ t := by simp [t,hi]
  refine ⟨fun i => f (toLex (i,0)),fun i => f (toLex (i,1)),?_,?_,?_⟩
  · simpa only [t, Finset.sum_map, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding,
      Finset.sum_product, Fin.sum_univ_two, Multiset.singleton_add, Multiset.insert_eq_cons] using hf
  · intro i hi
    exact hs _ (ht i hi 0) _ (ht i hi 1) (Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl,show (0 : Fin 2) ≤ 1 by decide⟩))
  · intro i hi j hj hij
    exact hs _ (ht i hi 1) _ (ht j hj 0) (Prod.Lex.toLex_le_toLex.mpr (Or.inl hij))

end NLS
