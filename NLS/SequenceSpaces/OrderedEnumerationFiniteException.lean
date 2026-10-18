import NLS.SequenceSpaces.OrderedEnumerationUnique
import Mathlib.Algebra.BigOperators.Finprod

/-! # Ordered enumerations with a finite exceptional set

Equal global multiplicities and fixed tails determine the entire ordered
enumeration, including repeated central entries.
-/

noncomputable section
open Set
open scoped Classical
namespace NLS

/-- Matching global multiplicities and fixed tails determine an ordered enumeration. -/
theorem ordered_enumeration_eq_of_finite_exception
    {α ι : Type*} [LinearOrder ι] (r : α → α → Prop) [Std.Antisymm r]
    (ξ η : ι → α) (s : Finset ι)
    (htail : ∀ n, n ∉ s → ξ n = η n)
    (hfinite : ∀ z, {n | η n = z}.Finite)
    (hmult : ∀ z, (∑ᶠ n, if ξ n = z then (1 : ℕ) else 0) =
      ∑ᶠ n, if η n = z then (1 : ℕ) else 0)
    (hξ : ∀ i j, i ≤ j → r (ξ i) (ξ j))
    (hη : ∀ i j, i ≤ j → r (η i) (η j)) : ξ = η := by
  have hcentral : (∑ n ∈ s, ({ξ n} : Multiset α)) = ∑ n ∈ s, ({η n} : Multiset α) := by
    apply Multiset.ext.mpr
    intro z
    let t := s ∪ (hfinite z).toFinset
    have hst : s ⊆ t := Finset.subset_union_left
    have hsξ : Function.support (fun n => if ξ n = z then (1 : ℕ) else 0) ⊆ t := by
      intro n hn
      have he : ξ n = z := by simpa using hn
      by_cases hns : n ∈ s
      · exact hst hns
      · apply Finset.mem_union_right
        exact (hfinite z).mem_toFinset.mpr ((htail n hns).symm.trans he)
    have hsη : Function.support (fun n => if η n = z then (1 : ℕ) else 0) ⊆ t := by
      intro n hn
      apply Finset.mem_union_right
      exact (hfinite z).mem_toFinset.mpr (by simpa using hn)
    have hcount := hmult z
    rw [finsum_eq_sum_of_support_subset _ hsξ,finsum_eq_sum_of_support_subset _ hsη] at hcount
    have hout : (∑ n ∈ t \ s, if ξ n = z then (1 : ℕ) else 0) =
        ∑ n ∈ t \ s, if η n = z then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [htail n (Finset.mem_sdiff.mp hn).2]
    have hc : (∑ n ∈ s, if ξ n = z then (1 : ℕ) else 0) =
        ∑ n ∈ s, if η n = z then (1 : ℕ) else 0 := by
      have hx := Finset.sum_sdiff (f := fun n => if ξ n = z then (1 : ℕ) else 0) hst
      have hy := Finset.sum_sdiff (f := fun n => if η n = z then (1 : ℕ) else 0) hst
      omega
    simpa only [Multiset.count_sum',Multiset.count_singleton,eq_comm] using hc
  funext n
  by_cases hn : n ∈ s
  · exact ordered_finset_multiset_enumeration_unique r s ξ η hcentral
      (fun i _ j _ hij => hξ i j hij) (fun i _ j _ hij => hη i j hij) n hn
  · exact htail n hn

end NLS
