import NLS.KdV.HillHminusOneCentralRoots
import NLS.KdV.HillHminusOneRealPairs
import NLS.SequenceSpaces.OrderedOneSidedEnumeration

/-! # Global ordered characteristic labels for real H^-1 potentials

The actual central count fixes the offset of the actual ordered high
pairs. Exhaustive exterior confinement ensures that every characteristic
root receives a label. Central and tail multiplicities are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped Classical
namespace NLS.KdV

/-- Assemble labels from the proved central control and actual high
pairs. No caller supplies a central root list or its cardinality. -/
theorem exists_hillHminus_characteristic_labels_of_control
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (N : ℕ) (h : HillHminusCentralControl q N) (r : ℝ) (hr : r ≤ Real.pi/4)
    (hpairs : ∀ k : ℕ, Nonempty (HillHminusRealHighPair q ⟨N+k,by have := h.index_ge_two; omega⟩ r))
    (hcover : ∀ z : ℂ, hillHminusRadicand q z = 0 → hillCentralSeparator N ≤ z.re →
      ∃ k : ℕ, z ∈ hillHminusGapSquareDisc ⟨N+k,by have := h.index_ge_two; omega⟩ r) :
    ∃ lambda : ℕ → ℝ, Monotone lambda ∧
      (∀ z : ℂ, hillHminusRadicand q z = 0 ↔ ∃ j : ℕ, z = (lambda j : ℂ)) ∧
      (∀ k : ℕ, ∃ p : HillHminusRealHighPair q ⟨N+k,by have := h.index_ge_two; omega⟩ r,
        lambda (2*(N+k)-1) = p.left ∧ lambda (2*(N+k)) = p.right) ∧
      (∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if lambda j = x then 1 else 0) =
        if (x : ℂ) ∈ hillCentralDisc N then analyticOrderNatAt (hillHminusRadicand q) x else 0) ∧
      ∀ j < 2*N-1, lambda j ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N) := by
  have hN := h.index_ge_two
  obtain ⟨xi,hxi,hxo,hxc⟩ := exists_ordered_hillHminusCentralRoots q hq N h
  let P (k : ℕ) : HillHminusRealHighPair q ⟨N+k,by omega⟩ r := Classical.choice (hpairs k)
  let lambda := NLS.appendPairedTail (2*N-1) xi (fun k => (P k).left) (fun k => (P k).right)
  have hxr (j : ℕ) (hj : j < 2*N-1) :
      xi j ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N) ∧ hillHminusRadicand q (xi j) = 0 := by
    apply (mem_hillHminusRealCentralRoots_iff q hq N h (xi j)).mp
    rw [← hxi]
    simp only [Multiset.mem_sum,Multiset.mem_singleton]
    exact ⟨j,Finset.mem_range.mpr hj,rfl⟩
  have hmono : Monotone lambda := by
    apply NLS.monotone_appendPairedTail (2*N-1) xi (fun k => (P k).left) (fun k => (P k).right) hxo
    · exact fun k => (P k).ordered
    · intro k
      exact ((P k).separated (P (k+1)) hr (by change N+k < N+(k+1); omega)).le
    · intro j hj
      exact (hxr j hj).1.2.le.trans
        ((P 0).above_central_separator hr N hN (by change N ≤ N+0; omega)).le
  have hroot (j : ℕ) : hillHminusRadicand q (lambda j) = 0 := by
    by_cases hj : j < 2*N-1
    · rw [show lambda j = xi j from NLS.appendPairedTail_prefix _ _ _ _ _ hj]
      exact (hxr j hj).2
    · dsimp only [lambda,NLS.appendPairedTail]
      rw [if_neg hj]
      split_ifs
      · exact (P _).pair.left_zero
      · exact (P _).pair.right_zero
  refine ⟨lambda,hmono,?_,?_,?_,?_⟩
  · intro z
    constructor
    · intro hz
      have him := hillHminusRadicand_root_im_zero q hq z hz
      have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
      by_cases hzc : z.re < hillCentralSeparator N
      · have hzmem : z.re ∈ hillHminusRealCentralRoots q N h :=
          (mem_hillHminusRealCentralRoots_iff q hq N h z.re).mpr
            ⟨⟨h.root_lower z hz,hzc⟩,by rwa [he]⟩
        rw [← hxi] at hzmem
        simp only [Multiset.mem_sum,Multiset.mem_singleton] at hzmem
        obtain ⟨j,hj,hjz⟩ := hzmem
        refine ⟨j,?_⟩
        rw [show lambda j = xi j from NLS.appendPairedTail_prefix _ _ _ _ _ (Finset.mem_range.mp hj)]
        rw [← hjz,he]
      · obtain ⟨k,hk⟩ := hcover z hz (le_of_not_gt hzc)
        rcases ((P k).pair.zeros_iff z hk).mp hz with hp | hp
        · refine ⟨(2*N-1)+2*k,?_⟩
          have hj : lambda ((2*N-1)+2*k) = (P k).left :=
            NLS.appendPairedTail_even (2*N-1) xi (fun k => (P k).left) (fun k => (P k).right) k
          exact hp.trans (congrArg Complex.ofReal hj).symm
        · refine ⟨(2*N-1)+2*k+1,?_⟩
          have hj : lambda ((2*N-1)+2*k+1) = (P k).right :=
            NLS.appendPairedTail_odd (2*N-1) xi (fun k => (P k).left) (fun k => (P k).right) k
          exact hp.trans (congrArg Complex.ofReal hj).symm
    · rintro ⟨j,rfl⟩
      exact hroot j
  · intro k
    refine ⟨P k,?_,?_⟩
    · have hj : 2*(N+k)-1 = (2*N-1)+2*k := by omega
      change NLS.appendPairedTail _ _ _ _ _ = _
      rw [hj,NLS.appendPairedTail_even]
    · have hj : 2*(N+k) = (2*N-1)+2*k+1 := by omega
      change NLS.appendPairedTail _ _ _ _ _ = _
      rw [hj,NLS.appendPairedTail_odd]
  · intro x
    rw [← hxc x]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show lambda j = xi j from NLS.appendPairedTail_prefix _ _ _ _ _ (Finset.mem_range.mp hj)]
  · intro j hj
    rw [show lambda j = xi j from NLS.appendPairedTail_prefix _ _ _ _ _ hj]
    exact (hxr j hj).1

/-- A common complex H^-1 neighborhood and one cutoff precede the
entire global real labeling. No roots are omitted in the central region
or between high discs. Cutoff-independent uniqueness is separate. -/
theorem exists_hillHminus_global_real_characteristic_labels (q : PeriodOneHminusOne) :
    ∃ r : ℝ, ∃ N : ℕ+, ∃ V : Set PeriodOneHminusOne,
      0 < r ∧ r ≤ Real.pi/4 ∧ 2 ≤ (N : ℕ) ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, IsRealPeriodOneHminusOne a → ∃ lambda : ℕ → ℝ,
        Monotone lambda ∧
        (∀ z : ℂ, hillHminusRadicand a z = 0 ↔ ∃ j : ℕ, z = (lambda j : ℂ)) ∧
        (∀ k : ℕ, ∃ p : HillHminusRealHighPair a ⟨(N : ℕ)+k,lt_of_lt_of_le N.property (Nat.le_add_right _ _)⟩ r,
          lambda (2*((N : ℕ)+k)-1) = p.left ∧ lambda (2*((N : ℕ)+k)) = p.right) ∧
        (∀ x : ℝ, (∑ j ∈ Finset.range (2*(N : ℕ)-1), if lambda j = x then 1 else 0) =
          if (x : ℂ) ∈ hillCentralDisc (N : ℕ) then analyticOrderNatAt (hillHminusRadicand a) x else 0) ∧
        ∀ j < 2*(N : ℕ)-1, lambda j ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator (N : ℕ)) := by
  obtain ⟨r,hr,hrpi,Np,Vp,_,hVp,hqp,hpairs⟩ := exists_hillHminus_real_high_pairs q
  obtain ⟨Nc,Vc,hNc,hVc,hqc,hregions⟩ := exists_hillHminus_source_root_regions q r hr
  let N := max Np Nc
  have hN : 2 ≤ N := hNc.trans (le_max_right _ _)
  refine ⟨r,⟨N,by omega⟩,Vp ∩ Vc,hr,hrpi,hN,hVp.inter hVc,⟨hqp,hqc⟩,?_⟩
  intro a ha hreal
  have hcontrol : HillHminusCentralControl a N := by
    refine ⟨hN,?_,?_⟩
    · intro s hs z hz
      exact (hregions N (le_max_right _ _) a ha.2 s hs z hz).1
    · intro s hs z hzc hz
      rcases (hregions N (le_max_right _ _) a ha.2 s hs z hz).2 with h | ⟨_,_,_,h⟩ <;> linarith
  apply exists_hillHminus_characteristic_labels_of_control a hreal N hcontrol r hrpi
  · intro k
    exact hpairs ⟨N+k,by omega⟩ (by change Np ≤ N+k; dsimp only [N]; omega) a ha.1 hreal
  · intro z hz hzc
    have hz' : hillHminusRadicand (((1 : ℝ) : ℂ) • a) z = 0 := by simpa using hz
    rcases (hregions N (le_max_right _ _) a ha.2 1 (by norm_num) z hz').2 with h | ⟨n,hn,hzn,_⟩
    · linarith
    · refine ⟨(n : ℕ)-N,?_⟩
      have he : (⟨N+((n : ℕ)-N),by omega⟩ : ℕ+) = n := by
        apply PNat.coe_injective
        change N+((n : ℕ)-N) = (n : ℕ)
        omega
      rw [he]
      have hc : ((Real.pi : ℂ)*(n : ℕ))^2 = (freeHillValue (n : ℕ) : ℂ) := by
        dsimp only [freeHillValue]; push_cast; ring
      change z ∈ closedBall (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)
      rw [hc]
      exact ball_subset_closedBall hzn

/-- The lowest characteristic energy exists intrinsically for every
real H^-1 potential; it is independent of the chosen labeling cutoff. -/
theorem exists_hillHminus_lowest_characteristic_root
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ x : ℝ, hillHminusRadicand q x = 0 ∧
      ∀ z : ℂ, hillHminusRadicand q z = 0 → x ≤ z.re := by
  obtain ⟨_,_,_,_,_,_,_,hqV,hlabels⟩ := exists_hillHminus_global_real_characteristic_labels q
  obtain ⟨lambda,hm,hroots,_⟩ := hlabels q hqV hq
  refine ⟨lambda 0,(hroots _).mpr ⟨0,rfl⟩,?_⟩
  intro z hz
  obtain ⟨j,hj⟩ := (hroots z).mp hz
  rw [hj,ofReal_re]
  exact hm (Nat.zero_le j)

def hillHminusLowestRealRoot (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) : ℝ :=
  (exists_hillHminus_lowest_characteristic_root q hq).choose

theorem hillHminusLowestRealRoot_spec (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    hillHminusRadicand q (hillHminusLowestRealRoot q hq) = 0 ∧
      ∀ z : ℂ, hillHminusRadicand q z = 0 → hillHminusLowestRealRoot q hq ≤ z.re :=
  (exists_hillHminus_lowest_characteristic_root q hq).choose_spec

theorem hillHminusLowestRealRoot_eq_of_minimal
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (x : ℝ)
    (hx : hillHminusRadicand q x = 0)
    (hmin : ∀ z : ℂ, hillHminusRadicand q z = 0 → x ≤ z.re) :
    x = hillHminusLowestRealRoot q hq := by
  have hs := hillHminusLowestRealRoot_spec q hq
  exact le_antisymm (by simpa only [ofReal_re] using hmin _ hs.1)
    (by simpa only [ofReal_re] using hs.2 x hx)

end NLS.KdV
