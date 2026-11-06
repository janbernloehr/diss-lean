import NLS.KdV.HillHminusOneGlobalRealLabels
import NLS.SequenceSpaces.OrderedNatEnumerationUnique

/-!
# Intrinsic full H-minus-one real characteristic labels

The shared central count and high pairs give an exhaustive ordered list.
Every occurrence is counted, including collapsed high pairs. Equality of
all multiplicities makes the list independent of its cutoff and radius.
-/
noncomputable section
open Set Metric
open scoped Classical
namespace NLS.KdV

structure HillHminusRealCharacteristicLabeling
    (q : PeriodOneHminusOne) (N : ℕ) (r : ℝ) (lambda : ℕ → ℝ) : Prop where
  cutoff_ge_two : 2 ≤ N
  radius_pos : 0 < r
  radius_le : r ≤ Real.pi/4
  monotone : Monotone lambda
  roots : ∀ z : ℂ, hillHminusRadicand q z = 0 ↔ ∃ j : ℕ, z = (lambda j : ℂ)
  high_pair : ∀ (n : ℕ) (hn : N ≤ n), ∃ p : HillHminusRealHighPair q ⟨n,by omega⟩ r,
    lambda (2*n-1) = p.left ∧ lambda (2*n) = p.right
  central_counts : ∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if lambda j = x then 1 else 0) =
    if (x : ℂ) ∈ hillCentralDisc N then analyticOrderNatAt (hillHminusRadicand q) x else 0
  central_mem : ∀ j < 2*N-1, lambda j ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N)

/-- Existence uses the proved full central count and actual high pairs;
no central root list or endpoint regularity is supplied by the caller. -/
theorem exists_hillHminusRealCharacteristicLabeling
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ lambda : ℕ → ℝ, ∃ N : ℕ, ∃ r : ℝ, HillHminusRealCharacteristicLabeling q N r lambda := by
  obtain ⟨r,N,V,hr,hrpi,hN,_,hqV,hlabels⟩ := exists_hillHminus_global_real_characteristic_labels q
  obtain ⟨lambda,hm,hroots,hpairs,hcounts,hmem⟩ := hlabels q hqV hq
  refine ⟨lambda,N,r,⟨hN,hr,hrpi,hm,hroots,?_,hcounts,hmem⟩⟩
  intro n hn
  have he : (N : ℕ)+(n-(N : ℕ)) = n := Nat.add_sub_of_le hn
  have hp := hpairs (n-(N : ℕ))
  have hpn : (⟨(N : ℕ)+(n-(N : ℕ)),by omega⟩ : ℕ+) = ⟨n,by omega⟩ := by
    apply PNat.coe_injective
    exact he
  rw [hpn] at hp
  simpa only [he] using hp

namespace HillHminusRealCharacteristicLabeling
variable {q : PeriodOneHminusOne} {N : ℕ} {r : ℝ} {lambda : ℕ → ℝ}

theorem root (h : HillHminusRealCharacteristicLabeling q N r lambda) (j : ℕ) :
    hillHminusRadicand q (lambda j) = 0 := (h.roots _).mpr ⟨j,rfl⟩

theorem high_slot (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (j : ℕ) (hj : 2*N-1 ≤ j) :
    N ≤ (j+1)/2 ∧ (j = 2*((j+1)/2)-1 ∨ j = 2*((j+1)/2)) := by
  have := h.cutoff_ge_two
  omega

theorem tail_above_separator (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (j : ℕ) (hj : 2*N-1 ≤ j) : hillCentralSeparator N < lambda j := by
  obtain ⟨hn,hslot⟩ := h.high_slot j hj
  obtain ⟨p,hl,hr⟩ := h.high_pair ((j+1)/2) hn
  have hp := p.above_central_separator h.radius_le N h.cutoff_ge_two hn
  rcases hslot with hs | hs
  · rw [hs,hl]
    exact hp
  · rw [hs,hr]
    exact hp.trans_le p.ordered

/-- A high value occurs only in its own two canonical slots. Strict
separation of the actual pairs also handles collapsed pairs. -/
theorem occurrence_mem_pair (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (x : ℝ) (n : ℕ) (hn : N ≤ n)
    (p : HillHminusRealHighPair q ⟨n,by have := h.cutoff_ge_two; omega⟩ r)
    (hxp : x = p.left ∨ x = p.right) (j : ℕ) (hj : lambda j = x) :
    j = 2*n-1 ∨ j = 2*n := by
  have hN := h.cutoff_ge_two
  have hpx : p.left ≤ x ∧ x ≤ p.right := by
    rcases hxp with rfl | rfl
    · exact ⟨le_rfl,p.ordered⟩
    · exact ⟨p.ordered,le_rfl⟩
  have hsep := p.above_central_separator h.radius_le N hN hn
  have hjhigh : 2*N-1 ≤ j := by
    by_contra! hjlow
    have hc := h.central_mem j hjlow
    rw [hj] at hc
    linarith [hc.2]
  obtain ⟨hm,hslot⟩ := h.high_slot j hjhigh
  obtain ⟨s,hl,hr⟩ := h.high_pair ((j+1)/2) hm
  have hsx : s.left ≤ x ∧ x ≤ s.right := by
    rcases hslot with hs | hs
    · have he : x = s.left := hj.symm.trans ((congrArg lambda hs).trans hl)
      exact ⟨he.symm.le,he.le.trans s.ordered⟩
    · have he : x = s.right := hj.symm.trans ((congrArg lambda hs).trans hr)
      exact ⟨s.ordered.trans he.symm.le,he.le⟩
  have hindex : (j+1)/2 = n := by
    rcases lt_trichotomy ((j+1)/2) n with hlt | he | hgt
    · have hd := s.separated p h.radius_le hlt
      change s.right < p.left at hd
      linarith
    · exact he
    · have hd := p.separated s h.radius_le hgt
      change p.right < s.left at hd
      linarith
  simpa only [hindex] using hslot

/-- The global occurrence count is exactly the full analytic order,
with finite occurrence sets for every real value. -/
theorem finite_support_and_multiplicity
    (h : HillHminusRealCharacteristicLabeling q N r lambda) (x : ℝ) :
    (fun j : ℕ => if lambda j = x then (1 : ℕ) else 0).HasFiniteSupport ∧
      (∑ᶠ j : ℕ, if lambda j = x then (1 : ℕ) else 0) =
        analyticOrderNatAt (hillHminusRadicand q) x := by
  have hN := h.cutoff_ge_two
  by_cases hd : hillHminusRadicand q x = 0
  · obtain ⟨j,hj⟩ := (h.roots x).mp hd
    have hjx : lambda j = x := (Complex.ofReal_injective hj).symm
    by_cases hx : x < hillCentralSeparator N
    · have hs : Function.support (fun i : ℕ => if lambda i = x then (1 : ℕ) else 0) ⊆
          (Finset.range (2*N-1) : Set ℕ) := by
        intro i hi
        have he : lambda i = x := by simpa using hi
        by_contra hi'
        have hh := h.tail_above_separator i (by simpa using hi')
        rw [he] at hh
        linarith
      have hjlow : j < 2*N-1 := by
        by_contra! hjhigh
        have hh := h.tail_above_separator j hjhigh
        rw [hjx] at hh
        linarith
      have hc := h.central_mem j hjlow
      rw [hjx] at hc
      have hxd : (x : ℂ) ∈ hillCentralDisc N :=
        (ofReal_mem_hillCentralDisc_iff N x).mpr ⟨hc.1.le,hc.2.le⟩
      refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
      rw [finsum_eq_sum_of_support_subset _ hs,h.central_counts x,if_pos hxd]
    · have hjhigh : 2*N-1 ≤ j := by
        by_contra! hjlow
        have hc := h.central_mem j hjlow
        rw [hjx] at hc
        exact hx hc.2
      obtain ⟨hn,hslot⟩ := h.high_slot j hjhigh
      let n := (j+1)/2
      obtain ⟨p,hl,hr⟩ := h.high_pair n hn
      have hxp : x = p.left ∨ x = p.right := by
        rcases hslot with hs | hs
        · exact Or.inl (hjx.symm.trans ((congrArg lambda hs).trans hl))
        · exact Or.inr (hjx.symm.trans ((congrArg lambda hs).trans hr))
      have hxd : (x : ℂ) ∈ hillHminusGapSquareDisc ⟨n,by omega⟩ r := by
        rcases hxp with rfl | rfl
        · exact ball_subset_closedBall p.pair.left_mem
        · exact ball_subset_closedBall p.pair.right_mem
      have hs : Function.support (fun i : ℕ => if lambda i = x then (1 : ℕ) else 0) ⊆
          ({2*n-1,2*n} : Finset ℕ) := by
        intro i hi
        have he : lambda i = x := by simpa using hi
        simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using
          h.occurrence_mem_pair x n hn p hxp i he
      refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
      rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_pair (show 2*n-1 ≠ 2*n by omega),hl,hr]
      simpa only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
        Complex.ofReal_inj,eq_comm,Nat.add_comm] using (p.pair.multiplicity x hxd).symm
  · have hs : Function.support (fun j : ℕ => if lambda j = x then (1 : ℕ) else 0) ⊆
        (∅ : Finset ℕ) := by
      intro j hj
      have he : lambda j = x := by simpa using hj
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

/-- Every cutoff and radius give the identical ordered list, including
every central repetition and every collapsed high pair. -/
theorem unique (h : HillHminusRealCharacteristicLabeling q N r lambda)
    {M : ℕ} {s : ℝ} {mu : ℕ → ℝ} (g : HillHminusRealCharacteristicLabeling q M s mu) :
    lambda = mu := by
  apply NLS.ordered_nat_enumeration_eq_of_multiplicity lambda mu
    h.finite_fiber g.finite_fiber h.monotone g.monotone
  intro x
  rw [(h.finite_support_and_multiplicity x).2,(g.finite_support_and_multiplicity x).2]

end HillHminusRealCharacteristicLabeling

/-- Intrinsic full H-minus-one labels in the usual slots lambda_0,
lambda_1^-,lambda_1^+,lambda_2^-,lambda_2^+,... . -/
def hillHminusLabels (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) : ℕ → ℝ :=
  (exists_hillHminusRealCharacteristicLabeling q hq).choose

theorem hillHminusLabels_spec (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, ∃ r : ℝ, HillHminusRealCharacteristicLabeling q N r (hillHminusLabels q hq) :=
  (exists_hillHminusRealCharacteristicLabeling q hq).choose_spec

theorem monotone_hillHminusLabels (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    Monotone (hillHminusLabels q hq) := by
  obtain ⟨_,_,h⟩ := hillHminusLabels_spec q hq
  exact h.monotone

theorem hillHminusLabels_roots_iff (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (z : ℂ) : hillHminusRadicand q z = 0 ↔ ∃ j : ℕ, z = (hillHminusLabels q hq j : ℂ) := by
  obtain ⟨_,_,h⟩ := hillHminusLabels_spec q hq
  exact h.roots z

theorem hillHminusLabels_finite_fiber (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (x : ℝ) : {j : ℕ | hillHminusLabels q hq j = x}.Finite := by
  obtain ⟨_,_,h⟩ := hillHminusLabels_spec q hq
  exact h.finite_fiber x

/-- Global label repetitions equal the full characteristic order. -/
theorem hillHminusLabels_global_multiplicity (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (x : ℝ) :
    (∑ᶠ j : ℕ, if hillHminusLabels q hq j = x then (1 : ℕ) else 0) =
      analyticOrderNatAt (hillHminusRadicand q) x := by
  obtain ⟨_,_,h⟩ := hillHminusLabels_spec q hq
  exact (h.finite_support_and_multiplicity x).2

/-- Any proved local construction is a specification of the intrinsic labels. -/
theorem hillHminusLabels_spec_at (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (N : ℕ) (r : ℝ) (lambda : ℕ → ℝ) (h : HillHminusRealCharacteristicLabeling q N r lambda) :
    HillHminusRealCharacteristicLabeling q N r (hillHminusLabels q hq) := by
  obtain ⟨_,_,g⟩ := hillHminusLabels_spec q hq
  rwa [h.unique g] at h

end NLS.KdV
