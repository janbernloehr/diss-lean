import NLS.KdV.HillHminusOneLabelFamilies
import NLS.KdV.HillHminusOnePairUniqueness
import NLS.SequenceSpaces.OrderedEnumerationFiniteException

/-! # Intrinsic uniqueness of the real H^-1 characteristic labels

Global analytic multiplicities and the ordered actual high pairs fix the
entire enumeration, independently of central cutoff or high-disc radius.
Repeated roots are retained rather than removed by a simple-root assumption.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped Classical
namespace NLS.KdV

theorem HillHminusRealHighPair.endpoints_unique
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ}
    (p : HillHminusRealHighPair q n r) (t : HillHminusRealHighPair q n s) :
    p.left = t.left ∧ p.right = t.right := by
  rcases p.pair.eq_or_swap t.pair with he | he
  · simpa only [ofReal_inj] using he
  · simp only [ofReal_inj] at he
    constructor <;> linarith [p.ordered,t.ordered]

theorem HillHminusRealHighPair.index_unique_of_common_endpoint
    {q : PeriodOneHminusOne} {n m : ℕ+} {r : ℝ}
    (p : HillHminusRealHighPair q n r) (t : HillHminusRealHighPair q m r)
    (hr : r ≤ Real.pi/4) (x : ℝ)
    (hp : x = p.left ∨ x = p.right) (ht : x = t.left ∨ x = t.right) : n = m := by
  apply PNat.coe_injective
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs := p.separated t hr h
    rcases hp with hp | hp <;> rcases ht with ht | ht <;> linarith [p.ordered,t.ordered]
  · have hs := t.separated p hr h
    rcases hp with hp | hp <;> rcases ht with ht | ht <;> linarith [p.ordered,t.ordered]

namespace HillHminusRealCharacteristicLabeling
variable {q : PeriodOneHminusOne} {N : ℕ} {r : ℝ} {lambda : ℕ → ℝ}

theorem cutoff_ge_two (h : HillHminusRealCharacteristicLabeling q N r lambda) : 2 ≤ N :=
  h.central_control.index_ge_two

theorem root (h : HillHminusRealCharacteristicLabeling q N r lambda) (j : ℕ) :
    hillHminusRadicand q (lambda j) = 0 := (h.roots _).mpr ⟨j,rfl⟩

theorem high_slot (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (j : ℕ) (hj : 2*N-1 ≤ j) :
    N ≤ (j+1)/2 ∧ (j = 2*((j+1)/2)-1 ∨ j = 2*((j+1)/2)) := by
  have hN := h.cutoff_ge_two
  omega

theorem tail_above_separator (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (j : ℕ) (hj : 2*N-1 ≤ j) : hillCentralSeparator N < lambda j := by
  obtain ⟨hn,hslot⟩ := h.high_slot j hj
  have hN := h.cutoff_ge_two
  let n : ℕ+ := ⟨(j+1)/2,by omega⟩
  obtain ⟨p,hl,hu⟩ := h.high_pair n hn
  have hp := p.above_central_separator h.radius_le N hN hn
  rcases hslot with hj' | hj'
  · rw [hj']
    change hillCentralSeparator N < lambda (2*(n : ℕ)-1)
    rw [hl]
    exact hp
  · rw [hj']
    change hillCentralSeparator N < lambda (2*(n : ℕ))
    rw [hu]
    exact hp.trans_le p.ordered

theorem occurrence_mem_pair (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (x : ℝ) (n : ℕ+) (hn : N ≤ (n : ℕ)) (p : HillHminusRealHighPair q n r)
    (hx : x = p.left ∨ x = p.right) (j : ℕ) (hj : lambda j = x) :
    j = 2*(n : ℕ)-1 ∨ j = 2*(n : ℕ) := by
  have hN := h.cutoff_ge_two
  have hxsep : hillCentralSeparator N < x := by
    have hp := p.above_central_separator h.radius_le N hN hn
    rcases hx with rfl | rfl
    · exact hp
    · exact hp.trans_le p.ordered
  have hjhigh : 2*N-1 ≤ j := by
    by_contra! hjlow
    have hm := h.central_mem j hjlow
    rw [hj] at hm
    linarith [hm.2]
  obtain ⟨hm,hslot⟩ := h.high_slot j hjhigh
  let m : ℕ+ := ⟨(j+1)/2,by omega⟩
  obtain ⟨t,hl,hu⟩ := h.high_pair m hm
  have hxt : x = t.left ∨ x = t.right := by
    rcases hslot with hs | hs
    · exact Or.inl (hj.symm.trans ((congrArg lambda hs).trans hl))
    · exact Or.inr (hj.symm.trans ((congrArg lambda hs).trans hu))
  have he := t.index_unique_of_common_endpoint p h.radius_le x hxt hx
  have he' : (j+1)/2 = (n : ℕ) := congrArg PNat.val he
  simpa only [he'] using hslot

/-- Every occurrence set is finite and its exact cardinality is the
analytic order of the actual H^-1 characteristic at the value. -/
theorem finite_support_and_multiplicity
    (h : HillHminusRealCharacteristicLabeling q N r lambda) (x : ℝ) :
    (fun j : ℕ => if lambda j = x then (1 : ℕ) else 0).HasFiniteSupport ∧
      (∑ᶠ j : ℕ, if lambda j = x then (1 : ℕ) else 0) =
        analyticOrderNatAt (hillHminusRadicand q) x := by
  have hN := h.cutoff_ge_two
  by_cases hd : hillHminusRadicand q x = 0
  · by_cases hx : x < hillCentralSeparator N
    · have hs : Function.support (fun j : ℕ => if lambda j = x then (1 : ℕ) else 0) ⊆
          (Finset.range (2*N-1) : Set ℕ) := by
        intro j hj
        have he : lambda j = x := by simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,
          one_ne_zero,imp_false,not_not] using hj
        by_contra hj'
        have hh := h.tail_above_separator j (by simpa only [Finset.mem_coe,Finset.mem_range,not_lt] using hj')
        rw [he] at hh
        linarith
      refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
      rw [finsum_eq_sum_of_support_subset _ hs,h.central_counts x]
      have hlo := h.central_control.root_lower x hd
      have hxd : (x : ℂ) ∈ hillCentralDisc N :=
        (ofReal_mem_hillCentralDisc_iff N x).mpr ⟨hlo.le,hx.le⟩
      rw [if_pos hxd]
    · obtain ⟨j,hj⟩ := (h.roots x).mp hd
      have hjx : lambda j = x := (ofReal_injective hj).symm
      have hjhigh : 2*N-1 ≤ j := by
        by_contra! hjlow
        have hm := h.central_mem j hjlow
        rw [hjx] at hm
        exact hx hm.2
      obtain ⟨hn,hslot⟩ := h.high_slot j hjhigh
      let n : ℕ+ := ⟨(j+1)/2,by omega⟩
      obtain ⟨p,hl,hu⟩ := h.high_pair n hn
      have hxp : x = p.left ∨ x = p.right := by
        rcases hslot with hs | hs
        · exact Or.inl (hjx.symm.trans ((congrArg lambda hs).trans hl))
        · exact Or.inr (hjx.symm.trans ((congrArg lambda hs).trans hu))
      have hxd : (x : ℂ) ∈ hillHminusGapSquareDisc n r := by
        rcases hxp with rfl | rfl
        · exact ball_subset_closedBall p.pair.left_mem
        · exact ball_subset_closedBall p.pair.right_mem
      have hs : Function.support (fun i : ℕ => if lambda i = x then (1 : ℕ) else 0) ⊆
          ({2*(n : ℕ)-1,2*(n : ℕ)} : Finset ℕ) := by
        intro i hi
        have he : lambda i = x := by simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,
          one_ne_zero,imp_false,not_not] using hi
        simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using
          h.occurrence_mem_pair x n hn p hxp i he
      refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
      rw [finsum_eq_sum_of_support_subset _ hs,
        Finset.sum_pair (show 2*(n : ℕ)-1 ≠ 2*(n : ℕ) by change 2*((j+1)/2)-1 ≠ 2*((j+1)/2); omega),hl,hu]
      have hc := p.pair.multiplicity x hxd
      simpa only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
        ofReal_inj,eq_comm,Nat.add_comm] using hc.symm
  · have hs : Function.support (fun j : ℕ => if lambda j = x then (1 : ℕ) else 0) ⊆
        (∅ : Finset ℕ) := by
      intro j hj
      have he : lambda j = x := by simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,
        one_ne_zero,imp_false,not_not] using hj
      exact (hd (he ▸ h.root j)).elim
    refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
    rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_empty]
    symm
    by_contra hne
    exact hd (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)

theorem finite_fiber (h : HillHminusRealCharacteristicLabeling q N r lambda) (x : ℝ) :
    {j : ℕ | lambda j = x}.Finite := by
  apply (h.finite_support_and_multiplicity x).1.subset
  intro j hj
  change (if lambda j = x then (1 : ℕ) else 0) ≠ 0
  have he : lambda j = x := hj
  rw [if_pos he]
  exact Nat.one_ne_zero

theorem tail_agrees {M : ℕ} {s : ℝ} {mu : ℕ → ℝ}
    (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (g : HillHminusRealCharacteristicLabeling q M s mu)
    (j : ℕ) (hj : 2*(max N M)-1 ≤ j) : lambda j = mu j := by
  have hN := h.cutoff_ge_two
  have hM := g.cutoff_ge_two
  have hn : N ≤ (j+1)/2 := by omega
  have hm : M ≤ (j+1)/2 := by omega
  let n : ℕ+ := ⟨(j+1)/2,by omega⟩
  obtain ⟨p,hpl,hpr⟩ := h.high_pair n hn
  obtain ⟨t,htl,htr⟩ := g.high_pair n hm
  have he := p.endpoints_unique t
  have hs : j = 2*(n : ℕ)-1 ∨ j = 2*(n : ℕ) := by
    change j = 2*((j+1)/2)-1 ∨ j = 2*((j+1)/2)
    omega
  rcases hs with hs | hs
  · rw [hs,hpl,htl,he.1]
  · rw [hs,hpr,htr,he.2]

/-- The entire ordered labeling is intrinsic, including repeated
central values and independently chosen high-disc radii. -/
theorem unique {M : ℕ} {s : ℝ} {mu : ℕ → ℝ}
    (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (g : HillHminusRealCharacteristicLabeling q M s mu) : lambda = mu := by
  apply NLS.ordered_enumeration_eq_of_finite_exception (· ≤ ·) lambda mu
    (Finset.range (2*(max N M)-1))
  · intro j hj
    exact h.tail_agrees g j (by simpa only [Finset.mem_range,not_lt] using hj)
  · exact g.finite_fiber
  · intro x
    exact (h.finite_support_and_multiplicity x).2.trans (g.finite_support_and_multiplicity x).2.symm
  · exact h.monotone
  · exact g.monotone

end HillHminusRealCharacteristicLabeling
end NLS.KdV
