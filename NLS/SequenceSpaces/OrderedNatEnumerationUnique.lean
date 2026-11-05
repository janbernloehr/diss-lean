import NLS.SequenceSpaces.OrderedEnumerationFiniteException

/-! Ordered natural-number enumerations with finite fibers are determined by
all their multiplicities; no agreement of tails is required. -/
noncomputable section
open Set
open scoped Classical
namespace NLS

/-- At the first strict discrepancy, the smaller entry occurs more often in
its own ordered enumeration than in the other one. -/
theorem multiplicity_lt_of_first_ordered_discrepancy {α : Type*} [LinearOrder α]
    (f g : ℕ → α) (hf : ∀ x, {i | f i = x}.Finite) (hg : Monotone g)
    (n : ℕ) (hprev : ∀ i < n, f i = g i) (hlt : f n < g n) :
    (∑ᶠ i, if g i = f n then (1:ℕ) else 0) <
      ∑ᶠ i, if f i = f n then (1:ℕ) else 0 := by
  have hgs : Function.support (fun i => if g i = f n then (1:ℕ) else 0) ⊆
      (Finset.range n : Set ℕ) := by
    intro i hi
    have he : g i = f n := by simpa using hi
    have hn : i < n := by
      by_contra hh
      have hm := hg (le_of_not_gt hh)
      rw [he] at hm
      exact (not_lt_of_ge hm) hlt
    exact Finset.mem_range.mpr hn
  let s := Finset.range (n+1) ∪ (hf (f n)).toFinset
  have hfs : Function.support (fun i => if f i = f n then (1:ℕ) else 0) ⊆ (s : Set ℕ) := by
    intro i hi
    apply Finset.mem_union_right
    exact (hf (f n)).mem_toFinset.mpr (by simpa using hi)
  rw [finsum_eq_sum_of_support_subset _ hgs, finsum_eq_sum_of_support_subset _ hfs]
  have hprefix : (∑ i ∈ Finset.range n, if g i = f n then (1:ℕ) else 0) =
      ∑ i ∈ Finset.range n, if f i = f n then (1:ℕ) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hprev i (Finset.mem_range.mp hi)]
  have hle : (∑ i ∈ Finset.range (n+1), if f i = f n then (1:ℕ) else 0) ≤
      ∑ i ∈ s, if f i = f n then (1:ℕ) else 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by intros; omega)
  rw [Finset.sum_range_succ, if_pos rfl] at hle
  rw [hprefix]
  omega

/-- Equal multiplicities determine the entire monotone enumeration, including
all repeated entries, without an assumed common tail. -/
theorem ordered_nat_enumeration_eq_of_multiplicity {α : Type*} [LinearOrder α]
    (f g : ℕ → α) (hf : ∀ x, {i | f i = x}.Finite) (hg : ∀ x, {i | g i = x}.Finite)
    (hfm : Monotone f) (hgm : Monotone g)
    (hmult : ∀ x, (∑ᶠ i, if f i = x then (1:ℕ) else 0) =
      ∑ᶠ i, if g i = x then (1:ℕ) else 0) : f = g := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases lt_trichotomy (f n) (g n) with hlt | he | hgt
    · have hh := multiplicity_lt_of_first_ordered_discrepancy f g hf hgm n ih hlt
      rw [hmult (f n)] at hh
      exact (lt_irrefl _ hh).elim
    · exact he
    · have hh := multiplicity_lt_of_first_ordered_discrepancy g f hg hfm n
        (fun i hi => (ih i hi).symm) hgt
      rw [hmult (g n)] at hh
      exact (lt_irrefl _ hh).elim

end NLS
