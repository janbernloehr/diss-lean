import NLS.KdV.HillCentralRoots
import NLS.KdV.HillRealGapPairs
import NLS.SequenceSpaces.OrderedOneSidedEnumeration

/-! # Ordered one-sided labels of the physical real Hill characteristic

The actual sorted central cluster is joined to the actual high endpoint
pairs. The central count fixes the offset, and localization orders the
tail. All labels are roots of the physical characteristic and every
physical characteristic root receives a label.
-/

noncomputable section
open Set Metric
open scoped Classical
namespace NLS.KdV

theorem HillRealHighGapPair.localization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    |p.left-freeHillValue n| ≤ 4*‖q‖ ∧ |p.right-freeHillValue n| ≤ 4*‖q‖ := by
  have hl := hillL2Radicand_zero_localization q hq n hn p.left
    (openHillStrip_subset n (hillClosedBall_subset_openStrip n hn p.left_mem)) hcut p.left_zero
  have hr := hillL2Radicand_zero_localization q hq n hn p.right
    (openHillStrip_subset n (hillClosedBall_subset_openStrip n hn p.right_mem)) hcut p.right_zero
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using And.intro hl hr

theorem HillRealHighGapPair.above_centralSeparator
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (n : ℕ) (hn : N ≤ n) (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    hillCentralSeparator N < p.left := by
  have hl := (p.localization q hq n (by omega) (hcut.trans (by exact_mod_cast hn))).1
  have hm := strictMono_freeHillValue.monotone hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold hillCentralSeparator
  linarith [(abs_le.mp hl).1]

theorem HillRealHighGapPair.separated
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n m : ℕ) (hn : 1 ≤ n) (hnm : n < m)
    (hcn : 16*‖q‖ ≤ (n : ℝ)) (hcm : 8*‖q‖ ≤ (m : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n)
    (r : HillRealHighGapPair (SpectralWeight.one.toCoeff q) m) : p.right < r.left := by
  have hp := (p.localization q hq n hn (by linarith [norm_nonneg q])).2
  have hr := (r.localization q hq m (by omega) hcm).1
  have hz : (freeHillValue n : ℂ) ∈ reducedHillStrip n := by
    simp [reducedHillStrip]
  have hs := freeHill_denominator_ge_index hn hz (k := (m : ℤ)) (by simpa using ne_of_gt hnm)
  have hmon := (strictMono_freeHillValue hnm).le
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hmon)] at hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  linarith [(abs_le.mp hp).2, (abs_le.mp hr).1]

/-- The actual real Hill characteristic has a global nondecreasing
one-sided labeling. The exact central count places each high pair in
the source slots 2*n-1 and 2*n, retaining its analytic multiplicities. -/
theorem exists_hillRealCharacteristicLabels
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 16*‖q‖ ≤ (N : ℝ)) :
    ∃ lambda : ℕ → ℝ, Monotone lambda ∧
      (∀ z : ℂ, hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0 ↔
        ∃ j : ℕ, z = (lambda j : ℂ)) ∧
      (∀ k : ℕ, ∃ p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) (N+k),
        lambda (2*(N+k)-1) = p.left ∧ lambda (2*(N+k)) = p.right) ∧
      (∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if lambda j = x then 1 else 0) =
        if (x : ℂ) ∈ hillCentralDisc N then
          analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x else 0) ∧
      ∀ j < 2*N-1, lambda j ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N) := by
  have hc8 : 8*‖q‖ ≤ (N : ℝ) := by linarith [norm_nonneg q]
  obtain ⟨xi,hxi,hxo,hxc⟩ := exists_ordered_hillCentralRoots q hq hreal N hN hc8
  let P (k : ℕ) : HillRealHighGapPair (SpectralWeight.one.toCoeff q) (N+k) :=
    Classical.choice (exists_hillRealHighGapPair q hq hreal (N+k) (by omega)
      (hcut.trans (by exact_mod_cast (show N ≤ N+k by omega))))
  let lambda := NLS.appendPairedTail (2*N-1) xi (fun k => (P k).left) (fun k => (P k).right)
  have hxr (j : ℕ) (hj : j < 2*N-1) :
      xi j ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N) ∧
        hillL2Radicand (SpectralWeight.one.toCoeff q) (xi j) = 0 := by
    apply (mem_hillRealCentralRoots_iff q hq hreal N hN hc8 (xi j)).mp
    rw [← hxi]
    simp only [Multiset.mem_sum, Multiset.mem_singleton]
    exact ⟨j,Finset.mem_range.mpr hj,rfl⟩
  have hmono : Monotone lambda := by
    apply NLS.monotone_appendPairedTail (2*N-1) xi (fun k => (P k).left) (fun k => (P k).right) hxo
    · exact fun k => (P k).ordered
    · intro k
      exact (HillRealHighGapPair.separated q hq (N+k) (N+(k+1)) (by omega) (by omega)
        (hcut.trans (by exact_mod_cast (show N ≤ N+k by omega)))
        (hc8.trans (by exact_mod_cast (show N ≤ N+(k+1) by omega))) (P k) (P (k+1))).le
    · intro j hj
      exact (hxr j hj).1.2.le.trans
        (HillRealHighGapPair.above_centralSeparator q hq N hN hc8 (N+0) (by omega) (P 0)).le
  have hroot (j : ℕ) : hillL2Radicand (SpectralWeight.one.toCoeff q) (lambda j) = 0 := by
    by_cases hj : j < 2*N-1
    · rw [show lambda j = xi j from NLS.appendPairedTail_prefix _ _ _ _ _ hj]
      exact (hxr j hj).2
    · dsimp only [lambda, NLS.appendPairedTail]
      rw [if_neg hj]
      split_ifs
      · exact (P _).left_zero
      · exact (P _).right_zero
  refine ⟨lambda,hmono,?_,?_,?_,?_⟩
  · intro z
    constructor
    · intro hd
      have him := hillL2Discriminant_root_im_zero q hq hreal z (sub_eq_zero.mp hd)
      have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
      by_cases hz : z.re < hillCentralSeparator N
      · have hzmem : z.re ∈ hillRealCentralRoots q hq N hN hc8 :=
          (mem_hillRealCentralRoots_iff q hq hreal N hN hc8 z.re).mpr
            ⟨⟨hillL2Radicand_re_lower_bound q hq N (by omega) hc8 z hd,hz⟩,by rwa [he]⟩
        rw [← hxi] at hzmem
        simp only [Multiset.mem_sum, Multiset.mem_singleton] at hzmem
        obtain ⟨j,hj,hjz⟩ := hzmem
        refine ⟨j,?_⟩
        rw [show lambda j = xi j from NLS.appendPairedTail_prefix _ _ _ _ _ (Finset.mem_range.mp hj)]
        rw [← hjz,he]
      · obtain ⟨n,hn,_,hzn⟩ := hillL2Radicand_real_high_cover q hq hreal N hN hc8 z
          (by exact le_of_not_gt hz) hd
        have hnk : N+(n-N) = n := by omega
        have hp := ((P (n-N)).zeros_iff z (by rwa [hnk])).mp hd
        rcases hp with hp | hp
        · refine ⟨(2*N-1)+2*(n-N),?_⟩
          have hj : lambda ((2*N-1)+2*(n-N)) = (P (n-N)).left :=
            NLS.appendPairedTail_even (2*N-1) xi (fun k => (P k).left) (fun k => (P k).right) (n-N)
          exact hp.trans (congrArg Complex.ofReal hj).symm
        · refine ⟨(2*N-1)+2*(n-N)+1,?_⟩
          have hj : lambda ((2*N-1)+2*(n-N)+1) = (P (n-N)).right :=
            NLS.appendPairedTail_odd (2*N-1) xi (fun k => (P k).left) (fun k => (P k).right) (n-N)
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

end NLS.KdV
