import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.KdV.HillHminusOutsideMiuraChart
import NLS.KdV.HillHminusOneMiuraRootSymmetry
import NLS.ZakharovShabat.SourceFiniteGapSobolev
import NLS.SequenceSpaces.PeriodOneMiuraSobolevImage

/-! # All Sobolev orders for actual real finite-gap rough Hill sources

The exact all-label Miura comparison preserves every collapsed positive
gap. Reflection controls negative indices. The real Dirac finite-gap
bootstrap then gives regularity of the ORIGINAL H-minus-one source, with
no initial L2 or Fourier-support assumption.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Squaring the positive Miura endpoints preserves collapse of EVERY
actual rough Hill gap, including the first gap. -/
theorem hillHminus_closed_gap_iff_miuraDirac_pair_eq
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ))≠0)
    (n : ℕ) (hn : 0<n) :
    hillHminusRealLabels q hq (2*n)=hillHminusRealLabels q hq (2*n-1) ↔
      hillMiuraDiracLeft u.val n=hillMiuraDiracRight u.val n := by
  obtain ⟨hL,hR⟩ := hillHminusLabels_pair_eq_squared_miuraDirac q hq u c himage hc n hn
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

open NLS.ZakharovShabat

/-- Eventual collapse of the actual rough Hill gaps makes its REAL Miura
source finite-gap, without Fourier-support or source-regularity assumptions. -/
theorem hillHminus_eventually_closed_miura_source_finiteGap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ))≠0)
    (N : ℕ) (hN : 1≤N)
    (hclosed : ∀ n : ℕ, N≤n → hillHminusRealLabels q hq (2*n)=hillHminusRealLabels q hq (2*n-1)) :
    (⟨hillMiuraDiagonal u.val,isRealType_hillMiuraDiagonal u⟩ : realTypeSourceLocus 2)∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
  classical
  have hpair (n : ℕ) (hn : N≤n) : hillMiuraDiracLeft u.val n=hillMiuraDiracRight u.val n :=
    (hillHminus_closed_gap_iff_miuraDirac_pair_eq q hq u c himage hc n (by omega)).mp (hclosed n hn)
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

theorem hillMiura_finiteGap_mem_sobolev
    (u : PeriodOneRealL2)
    (hf : (⟨hillMiuraDiagonal u.val,isRealType_hillMiuraDiagonal u⟩ : realTypeSourceLocus 2)∈
      sourceFiniteGapLocus (by simp) (by norm_num)) (s : ℝ) (hs : 0≤s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*u.val n) 2 := by
  have hd := (sourceFiniteGap_physical_mem_sobolev (by simp) (by norm_num)
    (⟨hillMiuraDiagonal u.val,isRealType_hillMiuraDiagonal u⟩ : realTypeSourceLocus 2) hf s hs).1
  simp only [hillMiuraDiagonal_fst] at hd
  let a : Coeff 2 := ⟨_,hd⟩
  have hh := lp.memℓp (Coeff.periodHalve a)
  apply hh.mono'
  intro n
  change ‖(Weight.sobolev s n : ℂ)*u.val n‖≤
    ‖(Weight.sobolev s (2*n) : ℂ)*Coeff.periodDouble u.val (2*n)‖
  rw [Coeff.periodDouble_even]
  simp only [norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos (Weight.positive _ _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.rpow_le_rpow (by positivity) _ hs
  norm_num only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith [abs_nonneg (n : ℝ)]
/-- Every REAL finite-gap distributional Hill source has all nonnegative
Sobolev orders. No initial L2 membership is required. -/
theorem hillHminus_real_finiteGap_mem_sobolev
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (N : ℕ) (hN : 1≤N)
    (hclosed : ∀ n : ℕ, N≤n → hillHminusRealLabels q hq (2*n)=hillHminusRealLabels q hq (2*n-1))
    (s : ℝ) (hs : 0≤s) : Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 := by
  obtain ⟨C,c,_,hc,hqC,hreal,houtside⟩ := exists_hillHminus_outside_real_Miura_chart q hq
  let u : PeriodOneRealL2 :=
    ⟨C.lift q,(periodOneL2Conjugation_fixed_iff _).mp (hreal q hqC hq)⟩
  have hi : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    simpa only [hc,ofReal_pow] using C.image q hqC
  have ho : hillHminusRadicand q (-((c^2 : ℝ) : ℂ))≠0 := by
    simpa only [hc,ofReal_pow] using houtside q hqC
  have hf := hillHminus_eventually_closed_miura_source_finiteGap q hq u (c^2) hi ho N hN hclosed
  exact periodOneMiura_image_mem_sobolev_of_all q u.val ((c^2 : ℝ) : ℂ) hi
    (fun t ht => hillMiura_finiteGap_mem_sobolev u hf t ht) s hs

end NLS.KdV
