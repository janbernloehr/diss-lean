import NLS.KdV.HillGlobalRealLabels
import NLS.SequenceSpaces.OrderedEnumerationFiniteException

/-! # Intrinsic real Hill characteristic labels

The global construction retains exact analytic multiplicities. Finite
root fibers and the intrinsic high pairs then force any two ordered
constructions to agree, even when their central cutoffs differ.
-/

noncomputable section
open Set Metric
open scoped Classical
namespace NLS.KdV

structure HillRealCharacteristicLabeling
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (N : ℕ) (lambda : ℕ → ℝ) : Prop where
  cutoff_ge_two : 2 ≤ N
  cutoff_bound : 16*‖q‖ ≤ (N : ℝ)
  monotone : Monotone lambda
  roots : ∀ z : ℂ, hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0 ↔
    ∃ j : ℕ, z = (lambda j : ℂ)
  high_pair : ∀ n : ℕ, N ≤ n → ∃ p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n,
    lambda (2*n-1) = p.left ∧ lambda (2*n) = p.right
  central_counts : ∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if lambda j = x then 1 else 0) =
    if (x : ℂ) ∈ hillCentralDisc N then
      analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x else 0
  central_mem : ∀ j < 2*N-1, lambda j ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N)

theorem exists_hillRealCharacteristicLabeling
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 16*‖q‖ ≤ (N : ℝ)) :
    ∃ lambda : ℕ → ℝ, HillRealCharacteristicLabeling q N lambda := by
  obtain ⟨lambda,hm,hr,hp,hc,hb⟩ := exists_hillRealCharacteristicLabels q hq hreal N hN hcut
  refine ⟨lambda,⟨hN,hcut,hm,hr,?_,hc,hb⟩⟩
  intro n hn
  have he : N+(n-N) = n := by omega
  have hp' := hp (n-N)
  rw [he] at hp'
  exact hp'

namespace HillRealCharacteristicLabeling
variable {q : WeightedCoeff SpectralWeight.one.toWeight 2} {N : ℕ} {lambda : ℕ → ℝ}

theorem cutoff_eight (h : HillRealCharacteristicLabeling q N lambda) : 8*‖q‖ ≤ (N : ℝ) := by
  linarith [h.cutoff_bound,norm_nonneg q]

theorem root (h : HillRealCharacteristicLabeling q N lambda) (j : ℕ) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) (lambda j) = 0 :=
  (h.roots _).mpr ⟨j,rfl⟩

/-- A high slot belongs to exactly the usual odd/even pair index. -/
theorem high_slot (h : HillRealCharacteristicLabeling q N lambda)
    (j : ℕ) (hj : 2*N-1 ≤ j) :
    N ≤ (j+1)/2 ∧ (j = 2*((j+1)/2)-1 ∨ j = 2*((j+1)/2)) := by
  have hn := h.cutoff_ge_two
  omega

theorem tail_above_separator (h : HillRealCharacteristicLabeling q N lambda)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (j : ℕ) (hj : 2*N-1 ≤ j) : hillCentralSeparator N < lambda j := by
  obtain ⟨hn,hj'⟩ := h.high_slot j hj
  obtain ⟨p,hl,hr⟩ := h.high_pair ((j+1)/2) hn
  have hp := p.above_centralSeparator q hq N h.cutoff_ge_two h.cutoff_eight _ hn
  rcases hj' with hj' | hj'
  · rw [hj',hl]
    exact hp
  · rw [hj',hr]
    exact hp.trans_le p.ordered

/-- An occurrence of a high root lies at one of its two own pair slots. -/
theorem occurrence_mem_pair (h : HillRealCharacteristicLabeling q N lambda)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (x : ℝ) (hx : hillCentralSeparator N ≤ x)
    (n : ℕ) (hn : N ≤ n) (hxn : (x : ℂ) ∈ reducedHillStrip n)
    (j : ℕ) (hj : lambda j = x) : j = 2*n-1 ∨ j = 2*n := by
  have hN := h.cutoff_ge_two
  have hjhigh : 2*N-1 ≤ j := by
    by_contra! hjlow
    have hm := h.central_mem j hjlow
    rw [hj] at hm
    linarith [hm.2]
  obtain ⟨hm,hslot⟩ := h.high_slot j hjhigh
  obtain ⟨p,hl,hr⟩ := h.high_pair ((j+1)/2) hm
  have hxm : (x : ℂ) ∈ reducedHillStrip ((j+1)/2) := by
    rcases hslot with hs | hs
    · have he : p.left = x := (hl.symm.trans (congrArg lambda hs).symm).trans hj
      rw [← he]
      exact openHillStrip_subset _ (hillClosedBall_subset_openStrip _ (by omega) p.left_mem)
    · have he : p.right = x := (hr.symm.trans (congrArg lambda hs).symm).trans hj
      rw [← he]
      exact openHillStrip_subset _ (hillClosedBall_subset_openStrip _ (by omega) p.right_mem)
  have hd : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0 := by
    rw [← hj]
    exact h.root j
  have hindex := hillL2Radicand_high_index_unique q hq ((j+1)/2) n (by omega) (by omega)
    (h.cutoff_eight.trans (by exact_mod_cast hm)) (h.cutoff_eight.trans (by exact_mod_cast hn))
    x hxm hxn hd
  simpa only [hindex] using hslot

/-- The full one-sided labeling retains the physical characteristic
orders, with finite occurrence sets, including at collapsed gaps. -/
theorem finite_support_and_multiplicity (h : HillRealCharacteristicLabeling q N lambda)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0) (x : ℝ) :
    (fun j : ℕ => if lambda j = x then (1 : ℕ) else 0).HasFiniteSupport ∧
      (∑ᶠ j : ℕ, if lambda j = x then (1 : ℕ) else 0) =
        analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x := by
  have hN := h.cutoff_ge_two
  by_cases hd : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0
  · by_cases hx : x < hillCentralSeparator N
    · have hs : Function.support (fun j : ℕ => if lambda j = x then (1 : ℕ) else 0) ⊆
          (Finset.range (2*N-1) : Set ℕ) := by
        intro j hj
        have he : lambda j = x := by simpa only [Function.mem_support, ne_eq, ite_eq_right_iff,
          one_ne_zero, imp_false, not_not] using hj
        by_contra hj'
        have hh := h.tail_above_separator hq j (by simpa only [Finset.mem_coe, Finset.mem_range,
          not_lt] using hj')
        rw [he] at hh
        linarith
      refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
      rw [finsum_eq_sum_of_support_subset _ hs, h.central_counts x]
      have hlo := hillL2Radicand_re_lower_bound q hq N (by omega) h.cutoff_eight x hd
      have hxd : (x : ℂ) ∈ hillCentralDisc N :=
        (ofReal_mem_hillCentralDisc_iff N x).mpr ⟨hlo.le,hx.le⟩
      rw [if_pos hxd]
    · obtain ⟨j,hj⟩ := (h.roots x).mp hd
      have hjx : lambda j = x := (Complex.ofReal_injective hj).symm
      have hjhigh : 2*N-1 ≤ j := by
        by_contra! hjlow
        have hm := h.central_mem j hjlow
        rw [hjx] at hm
        exact hx hm.2
      obtain ⟨hn,hslot⟩ := h.high_slot j hjhigh
      let n := (j+1)/2
      obtain ⟨p,hl,hr⟩ := h.high_pair n hn
      have hxp : x = p.left ∨ x = p.right := by
        rcases hslot with hs | hs
        · exact Or.inl (hjx.symm.trans ((congrArg lambda hs).trans hl))
        · exact Or.inr (hjx.symm.trans ((congrArg lambda hs).trans hr))
      have hxd : (x : ℂ) ∈ closedBall (freeHillValue n : ℂ) (n : ℝ) := by
        rcases hxp with rfl | rfl
        · exact p.left_mem
        · exact p.right_mem
      have hxn := openHillStrip_subset n (hillClosedBall_subset_openStrip n (by omega) hxd)
      have hs : Function.support (fun i : ℕ => if lambda i = x then (1 : ℕ) else 0) ⊆
          ({2*n-1,2*n} : Finset ℕ) := by
        intro i hi
        have he : lambda i = x := by simpa only [Function.mem_support, ne_eq, ite_eq_right_iff,
          one_ne_zero, imp_false, not_not] using hi
        simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using
          h.occurrence_mem_pair hq x (le_of_not_gt hx) n hn hxn i he
      refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
      rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair (show 2*n-1 ≠ 2*n by omega),hl,hr]
      have hc := p.orders x hxd
      simpa only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton,
        Complex.ofReal_inj, eq_comm, Nat.add_comm] using hc.symm
  · have hs : Function.support (fun j : ℕ => if lambda j = x then (1 : ℕ) else 0) ⊆
        (∅ : Finset ℕ) := by
      intro j hj
      have he : lambda j = x := by simpa only [Function.mem_support, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] using hj
      exact (hd (he ▸ h.root j)).elim
    refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
    rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_empty]
    symm
    by_contra hne
    exact hd (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)

theorem finite_fiber (h : HillRealCharacteristicLabeling q N lambda)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0) (x : ℝ) :
    {j : ℕ | lambda j = x}.Finite := by
  apply (h.finite_support_and_multiplicity hq x).1.subset
  intro j hj
  have he : lambda j = x := hj
  change (if lambda j = x then (1 : ℕ) else 0) ≠ 0
  rw [if_pos he]
  exact Nat.one_ne_zero

theorem tail_agrees {M : ℕ} {mu : ℕ → ℝ}
    (h : HillRealCharacteristicLabeling q N lambda) (g : HillRealCharacteristicLabeling q M mu)
    (j : ℕ) (hj : 2*(max N M)-1 ≤ j) : lambda j = mu j := by
  have hN := h.cutoff_ge_two
  have hM := g.cutoff_ge_two
  have hn : N ≤ (j+1)/2 := by omega
  have hm : M ≤ (j+1)/2 := by omega
  obtain ⟨p,hpl,hpr⟩ := h.high_pair ((j+1)/2) hn
  obtain ⟨r,hrl,hrr⟩ := g.high_pair ((j+1)/2) hm
  have he := p.endpoints_unique (SpectralWeight.one.toCoeff q) ((j+1)/2) (by omega) r
  have hs : j = 2*((j+1)/2)-1 ∨ j = 2*((j+1)/2) := by omega
  rcases hs with hs | hs
  · rw [hs,hpl,hrl,he.1]
  · rw [hs,hpr,hrr,he.2]

/-- The actual ordered labels are independent of the central cutoff and
of all choices in the finite or high root enumerations. -/
theorem unique {M : ℕ} {mu : ℕ → ℝ}
    (h : HillRealCharacteristicLabeling q N lambda) (g : HillRealCharacteristicLabeling q M mu)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0) : lambda = mu := by
  apply NLS.ordered_enumeration_eq_of_finite_exception (· ≤ ·) lambda mu
    (Finset.range (2*(max N M)-1))
  · intro j hj
    exact h.tail_agrees g j (by simpa only [Finset.mem_range, not_lt] using hj)
  · exact g.finite_fiber hq
  · intro x
    exact (h.finite_support_and_multiplicity hq x).2.trans
      (g.finite_support_and_multiplicity hq x).2.symm
  · exact h.monotone
  · exact g.monotone

end HillRealCharacteristicLabeling
end NLS.KdV
