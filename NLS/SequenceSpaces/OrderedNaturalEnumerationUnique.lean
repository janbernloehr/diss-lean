import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Ordered natural enumerations are fixed by their multiplicities

Unlike two-sided indexing, a natural enumeration has a first element.
No asymptotic tail or arbitrary offset is needed: finite fibers and equal
global multiplicities determine every ordered slot.
-/
noncomputable section
open Set
open scoped Classical
namespace NLS
variable {α : Type*} [LinearOrder α]

private theorem count_eq_card (ξ : ℕ → α) (x : α) (h : {n | ξ n = x}.Finite) :
    (∑ᶠ n : ℕ, if ξ n = x then (1 : ℕ) else 0) = h.toFinset.card := by
  calc
    _ = ∑ n ∈ h.toFinset, if ξ n = x then (1 : ℕ) else 0 :=
      finsum_eq_sum_of_support_subset _ (by
        intro n hn
        apply h.mem_toFinset.mpr
        change ξ n = x
        simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hn)
    _ = ∑ _n ∈ h.toFinset, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos (show ξ n = x from h.mem_toFinset.mp hn)]
    _ = _ := by simp

private theorem not_lt_of_prefix_counts (ξ η : ℕ → α) (n : ℕ)
    (hξ : ∀ x, {j | ξ j = x}.Finite) (hη : ∀ x, {j | η j = x}.Finite)
    (hm : ∀ x, (∑ᶠ j : ℕ, if ξ j = x then (1 : ℕ) else 0) =
      ∑ᶠ j : ℕ, if η j = x then (1 : ℕ) else 0)
    (hmono : Monotone η) (hprefix : ∀ j < n, ξ j = η j) : ¬ξ n < η n := by
  intro hlt
  let x := ξ n
  let A := (hξ x).toFinset
  let B := (hη x).toFinset
  have hsub : B ⊆ A := by
    intro j hj
    have he : η j = x := (hη x).mem_toFinset.mp hj
    have hjn : j < n := by
      by_contra hn
      have hle := hmono (le_of_not_gt hn)
      rw [he] at hle
      exact (not_le_of_gt hlt) hle
    exact (hξ x).mem_toFinset.mpr ((hprefix j hjn).trans he)
  have hnA : n ∈ A := (hξ x).mem_toFinset.mpr rfl
  have hnB : n ∉ B := by
    intro hn
    exact hlt.ne ((hη x).mem_toFinset.mp hn).symm
  have hss : B ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
    intro he
    exact hnB (he.symm ▸ hnA)⟩
  have hc := Finset.card_lt_card hss
  have he := hm x
  rw [count_eq_card ξ x (hξ x),count_eq_card η x (hη x)] at he
  change A.card = B.card at he
  omega

theorem ordered_natural_enumeration_unique (ξ η : ℕ → α)
    (hξ : Monotone ξ) (hη : Monotone η)
    (hfiniteξ : ∀ x, {n | ξ n = x}.Finite) (hfiniteη : ∀ x, {n | η n = x}.Finite)
    (hmult : ∀ x, (∑ᶠ n : ℕ, if ξ n = x then (1 : ℕ) else 0) =
      ∑ᶠ n : ℕ, if η n = x then (1 : ℕ) else 0) : ξ = η := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_contra he
    rcases lt_or_gt_of_ne he with h | h
    · exact not_lt_of_prefix_counts ξ η n hfiniteξ hfiniteη hmult hη ih h
    · exact not_lt_of_prefix_counts η ξ n hfiniteη hfiniteξ
        (fun x => (hmult x).symm) hξ (fun j hj => (ih j hj).symm) h

end NLS
