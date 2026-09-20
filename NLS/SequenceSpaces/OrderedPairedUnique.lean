import NLS.SequenceSpaces.OrderedEnumerationUnique
import NLS.SequenceSpaces.OrderedPairedEnumeration

/-!
# Uniqueness of ordered paired enumerations

View the two slots at each index as a lexicographic product with Fin 2.
Within-pair and between-pair order make the combined enumeration ordered,
so equal multisets determine both coordinates, including repeated values.
-/

noncomputable section
namespace NLS

/-- Equal ordered two-element multisets have equal first and second entries. -/
theorem ordered_pair_unique {α : Type*} (r : α → α → Prop) [Std.Antisymm r]
    (x y a b : α) (he : ({x,y} : Multiset α) = {a,b}) (hxy : r x y) (hab : r a b) :
    x = a ∧ y = b := by
  have hp : List.Perm [x,y] [a,b] := Multiset.coe_eq_coe.mp he
  have hh := hp.eq_of_pairwise' (by simpa using hxy) (by simpa using hab)
  simpa only [List.cons.injEq, and_true] using hh

/-- Within-pair and between-pair order induce order on the lexicographic slot indices. -/
theorem ordered_paired_slots {α ι : Type*} [LinearOrder ι]
    (r : α → α → Prop) [IsTrans α r] [Std.Refl r] (s : Finset ι) (ξ η : ι → α)
    (hw : ∀ i ∈ s, r (ξ i) (η i)) (hc : ∀ i ∈ s, ∀ j ∈ s, i < j → r (η i) (ξ j))
    (i j : ι) (hi : i ∈ s) (hj : j ∈ s) (a b : Fin 2)
    (hab : toLex (i,a) ≤ toLex (j,b)) :
    r (if a = 0 then ξ i else η i) (if b = 0 then ξ j else η j) := by
  have ht : ∀ {x y z : α}, r x y → r y z → r x z := fun h₁ h₂ => IsTrans.trans _ _ _ h₁ h₂
  rcases Prod.Lex.toLex_le_toLex.mp hab with hij | ⟨hij,hab⟩
  · have hh := hc i hi j hj hij
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp only [ha,hb,ite_true,ite_false]
    · exact ht (hw i hi) hh
    · exact ht (ht (hw i hi) hh) (hw j hj)
    · exact hh
    · exact ht hh (hw j hj)
  · change i = j at hij
    change a ≤ b at hab
    subst j
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp only [ha,hb,ite_true,ite_false]
    · exact Std.Refl.refl _
    · exact hw i hi
    · have : a = 0 := by omega
      exact (ha this).elim
    · exact Std.Refl.refl _

/-- Equal paired multisets and paired order fix both coordinates at every finite index. -/
theorem ordered_paired_multiset_enumeration_unique {α ι : Type*} [LinearOrder ι]
    (r : α → α → Prop) [IsTrans α r] [Std.Refl r] [Std.Antisymm r]
    (s : Finset ι) (ξ η a b : ι → α)
    (he : (∑ i ∈ s, ({ξ i,η i} : Multiset α)) = ∑ i ∈ s, ({a i,b i} : Multiset α))
    (hw : ∀ i ∈ s, r (ξ i) (η i)) (hc : ∀ i ∈ s, ∀ j ∈ s, i < j → r (η i) (ξ j))
    (hw' : ∀ i ∈ s, r (a i) (b i)) (hc' : ∀ i ∈ s, ∀ j ∈ s, i < j → r (b i) (a j)) :
    ∀ i ∈ s, ξ i = a i ∧ η i = b i := by
  classical
  let t : Finset (ι ×ₗ Fin 2) := (s ×ˢ Finset.univ).map toLex.toEmbedding
  let F (x y : ι → α) (k : ι ×ₗ Fin 2) := if (ofLex k).2 = 0 then x (ofLex k).1 else y (ofLex k).1
  have hsum (x y : ι → α) : (∑ k ∈ t, ({F x y k} : Multiset α)) = ∑ i ∈ s, ({x i,y i} : Multiset α) := by
    simp [t,F,Finset.sum_product,Fin.sum_univ_two,Multiset.singleton_add]
  have horder (x y : ι → α) (hw : ∀ i ∈ s, r (x i) (y i))
      (hc : ∀ i ∈ s, ∀ j ∈ s, i < j → r (y i) (x j)) :
      ∀ i ∈ t, ∀ j ∈ t, i ≤ j → r (F x y i) (F x y j) := by
    intro i hi j hj hij
    have hi' : (ofLex i).1 ∈ s := by simpa [t] using hi
    have hj' : (ofLex j).1 ∈ s := by simpa [t] using hj
    exact ordered_paired_slots r s x y hw hc (ofLex i).1 (ofLex j).1 hi' hj' (ofLex i).2 (ofLex j).2 hij
  have hu := ordered_finset_multiset_enumeration_unique r t (F ξ η) (F a b)
    ((hsum ξ η).trans (he.trans (hsum a b).symm)) (horder ξ η hw hc) (horder a b hw' hc')
  intro i hi
  have h0 := hu (toLex (i,0)) (by simp [t,hi])
  have h1 := hu (toLex (i,1)) (by simp [t,hi])
  exact ⟨by simpa [F] using h0,by simpa [F] using h1⟩

end NLS
