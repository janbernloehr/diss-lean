import NLS.KdV.HillMiuraGroundLabels
import NLS.KdV.HillHminusFiniteGapSobolev
import NLS.KdV.HillMiuraFiniteGapEnergyBound

/-! # Actual finite-gap ground factors for rough Hill finite-gap sources

Eventual collapse of the original rough Hill gaps forces actual spectral
finite-gap support of every normalized real factor. The unconditional
ground factor therefore satisfies the proved weak Dirac-action bound.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminus_closed_gap_iff_miuraDirac_pair_eq_of_meanZero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hm : u.val 0 = 0)
    (n : ℕ) (hn : 0<n) :
    hillHminusRealLabels q hq (2*n)=hillHminusRealLabels q hq (2*n-1) ↔
      hillMiuraDiracLeft u.val n=hillMiuraDiracRight u.val n := by
  obtain ⟨hL,hR⟩ := hillHminusLabels_pair_eq_squared_miuraDirac_of_meanZero q hq u c himage hm n hn
  rw [hL,hR]
  constructor
  · intro he
    have hpos := hillMiura_positive_gap_left_pos u (n : ℤ) (by exact_mod_cast hn)
    have hord := hillMiuraDiracPair_ordered u.val n
    have hre : (hillMiuraDiracLeft u.val n).re=(hillMiuraDiracRight u.val n).re := by
      change 0<(hillMiuraDiracLeft u.val n).re at hpos
      nlinarith
    exact Complex.ext hre ((hillMiuraDiracPair_real u n).1.trans (hillMiuraDiracPair_real u n).2.symm)
  · intro he
    rw [he]

theorem hillHminus_eventually_closed_ground_source_finiteGap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hm : u.val 0 = 0)
    (N : ℕ) (hN : 1≤N)
    (hclosed : ∀ n : ℕ, N≤n → hillHminusRealLabels q hq (2*n)=hillHminusRealLabels q hq (2*n-1)) :
    (⟨hillMiuraDiagonal u.val,isRealType_hillMiuraDiagonal u⟩ : realTypeSourceLocus 2)∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
  classical
  have hpair (n : ℕ) (hn : N≤n) : hillMiuraDiracLeft u.val n=hillMiuraDiracRight u.val n :=
    (hillHminus_closed_gap_iff_miuraDirac_pair_eq_of_meanZero q hq u c himage hm n (by omega)).mp (hclosed n hn)
  change {j : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) j≠0}.Finite
  apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  intro j hj
  by_contra hout
  apply hj
  change hillMiuraDiracRight u.val j-hillMiuraDiracLeft u.val j=0
  cases j with
  | ofNat n =>
    have hn : N≤n := by simp only [Set.mem_Icc,Int.ofNat_eq_natCast] at hout; omega
    exact sub_eq_zero.mpr (hpair n hn).symm
  | negSucc n =>
    have hn : N≤n+1 := by simp only [Set.mem_Icc] at hout; omega
    have hneg := hillMiuraCanonicalEndpoints_neg u.val ((n+1 : ℕ) : ℤ)
    change hillMiuraDiracLeft u.val (-((n+1 : ℕ) : ℤ)) = -hillMiuraDiracRight u.val (n+1) ∧
      hillMiuraDiracRight u.val (-((n+1 : ℕ) : ℤ)) = -hillMiuraDiracLeft u.val (n+1) at hneg
    change hillMiuraDiracRight u.val (-((n+1 : ℕ) : ℤ))-
      hillMiuraDiracLeft u.val (-((n+1 : ℕ) : ℤ))=0
    rw [hneg.1,hneg.2]
    have hp : hillMiuraDiracLeft u.val ((n : ℤ)+1)=hillMiuraDiracRight u.val ((n : ℤ)+1) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hpair (n+1) hn
    rw [hp,sub_self]


/-- Every actual real mean-zero rough Hill finite-gap source has a genuine
normalized spectral finite-gap ground factor and the actual Dirac bound. -/
theorem exists_finiteGap_ground_factor_with_energy_bound
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hclosed : ∀ n : ℕ, N ≤ n → hillHminusRealLabels q hq (2*n)=hillHminusRealLabels q hq (2*n-1)) :
    ∃ u : PeriodOneRealL2, u.val 0 = 0 ∧
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (-hillHminusLowestRealRoot q hq : ℝ)) ∧
      ‖u.val‖^2 = -hillHminusLowestRealRoot q hq ∧
      ∃ hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num),
        -hillHminusLowestRealRoot q hq ≤ ∑ n ∈ hf.toFinset,
          sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) := by
  obtain ⟨u,hu,hi,hn,_ht,_hl,_hr,_ha⟩ := exists_periodOneMiura_ground_factor q hq hm
  have hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num) :=
    hillHminus_eventually_closed_ground_source_finiteGap q hq u _ hi hu N hN hclosed
  refine ⟨u,hu,hi,hn,hf,?_⟩
  rw [←hn]
  exact hillMiura_finiteGap_norm_sq_le_weak_weighted_actions u hu hf

end NLS.KdV
