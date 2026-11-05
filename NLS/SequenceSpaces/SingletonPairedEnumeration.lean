import NLS.SequenceSpaces.OrderedNatEnumerationUnique
import Mathlib.Tactic

/-! # One initial point followed by ordered pairs

The natural slots are a₀,l₁,r₁,l₂,r₂,... . Strict separation of different
pairs preserves every repetition within a pair and gives exact finite
fibers and occurrence counts, including collapsed pairs.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped Classical
namespace NLS
variable {α : Type*}

def singletonPairedEnumeration (a : α) (l r : ℕ → α) (j : ℕ) : α :=
  if j = 0 then a else if j % 2 = 1 then l ((j+1)/2) else r (j/2)

@[simp] theorem singletonPairedEnumeration_zero (a : α) (l r : ℕ → α) :
    singletonPairedEnumeration a l r 0 = a := by simp [singletonPairedEnumeration]

theorem singletonPairedEnumeration_left (a : α) (l r : ℕ → α) (n : ℕ) (hn : 0 < n) :
    singletonPairedEnumeration a l r (2*n-1) = l n := by
  have hzero : 2*n-1 ≠ 0 := by omega
  have hmod : (2*n-1)%2 = 1 := by omega
  have hdiv : (2*n-1+1)/2 = n := by omega
  simp only [singletonPairedEnumeration,if_neg hzero,if_pos hmod,hdiv]

theorem singletonPairedEnumeration_right (a : α) (l r : ℕ → α) (n : ℕ) (hn : 0 < n) :
    singletonPairedEnumeration a l r (2*n) = r n := by
  have hzero : 2*n ≠ 0 := by omega
  have hmod : (2*n)%2 ≠ 1 := by omega
  have hdiv : 2*n/2 = n := by omega
  simp only [singletonPairedEnumeration,if_neg hzero,if_neg hmod,hdiv]

theorem singletonPairedEnumeration_slot (j : ℕ) (hj : j ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (j = 2*n-1 ∨ j = 2*n) := by
  exact ⟨(j+1)/2,by omega,by omega⟩

variable [LinearOrder α]

theorem singletonPairedEnumeration_mem_pair (a : α) (l r : ℕ → α)
    (hpair : ∀ n : ℕ, 0 < n → l n ≤ r n) (j : ℕ) (hj : j ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (j = 2*n-1 ∨ j = 2*n) ∧
      singletonPairedEnumeration a l r j ∈ Icc (l n) (r n) := by
  obtain ⟨n,hn,hslot⟩ := singletonPairedEnumeration_slot j hj
  refine ⟨n,hn,hslot,?_⟩
  rcases hslot with rfl | rfl
  · rw [singletonPairedEnumeration_left a l r n hn]
    exact ⟨le_rfl,hpair n hn⟩
  · rw [singletonPairedEnumeration_right a l r n hn]
    exact ⟨hpair n hn,le_rfl⟩

theorem monotone_singletonPairedEnumeration (a : α) (l r : ℕ → α)
    (hstart : ∀ n : ℕ, 0 < n → a < l n)
    (hpair : ∀ n : ℕ, 0 < n → l n ≤ r n)
    (hcross : ∀ i : ℕ, 0 < i → ∀ j : ℕ, i < j → r i < l j) :
    Monotone (singletonPairedEnumeration a l r) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    rw [singletonPairedEnumeration_zero]
    by_cases hj : j = 0
    · subst j; simp
    · obtain ⟨n,hn,_,hb⟩ := singletonPairedEnumeration_mem_pair a l r hpair j hj
      exact (hstart n hn).le.trans hb.1
  · have hj : j ≠ 0 := by omega
    obtain ⟨n,hn,hiS,hiB⟩ := singletonPairedEnumeration_mem_pair a l r hpair i hi
    obtain ⟨m,hm,hjS,hjB⟩ := singletonPairedEnumeration_mem_pair a l r hpair j hj
    have hnm : n ≤ m := by rcases hiS with h | h <;> rcases hjS with h' | h' <;> omega
    rcases lt_or_eq_of_le hnm with hlt | he
    · exact hiB.2.trans ((hcross n hn m hlt).le.trans hjB.1)
    · subst m
      rcases hiS with hiS | hiS <;> rcases hjS with hjS | hjS
      · have he : i = j := by omega
        rw [he]
      · rw [hiS,hjS,singletonPairedEnumeration_left a l r n hn,
          singletonPairedEnumeration_right a l r n hn]
        exact hpair n hn
      · exact False.elim (by omega)
      · have he : i = j := by omega
        rw [he]

theorem singletonPairedEnumeration_fiber_at_pair (a : α) (l r : ℕ → α)
    (hstart : ∀ n : ℕ, 0 < n → a < l n)
    (hpair : ∀ n : ℕ, 0 < n → l n ≤ r n)
    (hcross : ∀ i : ℕ, 0 < i → ∀ j : ℕ, i < j → r i < l j)
    (n : ℕ) (hn : 0 < n) (x : α) (hx : x ∈ Icc (l n) (r n))
    (j : ℕ) (hj : singletonPairedEnumeration a l r j = x) : j = 2*n-1 ∨ j = 2*n := by
  by_cases hj0 : j = 0
  · subst j
    rw [singletonPairedEnumeration_zero] at hj
    exact False.elim ((hstart n hn).not_ge (hx.1.trans hj.symm.le))
  · obtain ⟨m,hm,hslot,hb⟩ := singletonPairedEnumeration_mem_pair a l r hpair j hj0
    rw [hj] at hb
    rcases lt_trichotomy m n with h | h | h
    · exact False.elim ((hcross m hm n h).not_ge (hx.1.trans hb.2))
    · simpa only [h] using hslot
    · exact False.elim ((hcross n hn m h).not_ge (hb.1.trans hx.2))

theorem singletonPairedEnumeration_finite_fiber (a : α) (l r : ℕ → α)
    (hstart : ∀ n : ℕ, 0 < n → a < l n)
    (hpair : ∀ n : ℕ, 0 < n → l n ≤ r n)
    (hcross : ∀ i : ℕ, 0 < i → ∀ j : ℕ, i < j → r i < l j) (x : α) :
    {j : ℕ | singletonPairedEnumeration a l r j = x}.Finite := by
  by_cases hx : ∃ j : ℕ, singletonPairedEnumeration a l r j = x
  · obtain ⟨j,hj⟩ := hx
    by_cases hj0 : j = 0
    · subst j
      rw [singletonPairedEnumeration_zero] at hj
      apply (Set.finite_singleton 0).subset
      intro k hk
      by_contra hk0
      obtain ⟨n,hn,_,hb⟩ := singletonPairedEnumeration_mem_pair a l r hpair k hk0
      rw [hk,← hj] at hb
      exact (hstart n hn).not_ge hb.1
    · obtain ⟨n,hn,_,hb⟩ := singletonPairedEnumeration_mem_pair a l r hpair j hj0
      rw [hj] at hb
      apply (Set.toFinite ({2*n-1,2*n} : Set ℕ)).subset
      intro k hk
      exact singletonPairedEnumeration_fiber_at_pair a l r hstart hpair hcross n hn x hb k hk
  · have he : {j : ℕ | singletonPairedEnumeration a l r j = x} = ∅ := by
      ext j; simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]; exact fun h => hx ⟨j,h⟩
    rw [he]; exact finite_empty

theorem singletonPairedEnumeration_count_pair (a : α) (l r : ℕ → α)
    (hstart : ∀ n : ℕ, 0 < n → a < l n)
    (hpair : ∀ n : ℕ, 0 < n → l n ≤ r n)
    (hcross : ∀ i : ℕ, 0 < i → ∀ j : ℕ, i < j → r i < l j)
    (n : ℕ) (hn : 0 < n) (x : α) (hx : x ∈ Icc (l n) (r n)) :
    (∑ᶠ j : ℕ, if singletonPairedEnumeration a l r j = x then (1 : ℕ) else 0) =
      (if l n = x then 1 else 0)+(if r n = x then 1 else 0) := by
  have hs : Function.support (fun j => if singletonPairedEnumeration a l r j = x then (1 : ℕ) else 0) ⊆
      ({2*n-1,2*n} : Finset ℕ) := by
    intro j hj
    have he : singletonPairedEnumeration a l r j = x := by simpa using hj
    simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using
      singletonPairedEnumeration_fiber_at_pair a l r hstart hpair hcross n hn x hx j he
  rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_pair (show 2*n-1 ≠ 2*n by omega),
    singletonPairedEnumeration_left a l r n hn,singletonPairedEnumeration_right a l r n hn]

theorem singletonPairedEnumeration_count_initial (a : α) (l r : ℕ → α)
    (hstart : ∀ n : ℕ, 0 < n → a < l n)
    (hpair : ∀ n : ℕ, 0 < n → l n ≤ r n) :
    (∑ᶠ j : ℕ, if singletonPairedEnumeration a l r j = a then (1 : ℕ) else 0) = 1 := by
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    obtain ⟨n,hn,_,hb⟩ := singletonPairedEnumeration_mem_pair a l r hpair j hj
    rw [if_neg (ne_of_gt ((hstart n hn).trans_le hb.1))]

end NLS
