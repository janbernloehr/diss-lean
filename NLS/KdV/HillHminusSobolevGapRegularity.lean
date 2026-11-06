import NLS.SequenceSpaces.PositiveHalfMembership
import NLS.KdV.HillMiuraEndpointSumBounds
import NLS.KdV.HillHminusMiuraSobolevRegularity
import NLS.KdV.HillHminusOneMiuraRootSymmetry

/-! # Native Sobolev regularity from the ORIGINAL rough Hill energy gaps

The literal energy gap is the actual Dirac gap times the positive endpoint
sum. Its bracket comparison transfers the exact all-order Miura criterion
to the original Hill labels, including every low and collapsed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The ORIGINAL positive Hill energy gaps, zero extended to nonpositive
integer indices. No unweighted summability of these raw gaps is asserted. -/
def hillHminusPositiveEnergyGap (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (j : ℤ) : ℂ :=
  if 0<j then ((hillHminusRealLabels q hr (2*j.toNat)-
    hillHminusRealLabels q hr (2*j.toNat-1) : ℝ) : ℂ) else 0

@[simp] theorem hillHminusPositiveEnergyGap_apply_nat
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusPositiveEnergyGap q hr (n : ℤ)=
      ((hillHminusRealLabels q hr (2*(n : ℕ))-
        hillHminusRealLabels q hr (2*(n : ℕ)-1) : ℝ) : ℂ) := by
  simp only [hillHminusPositiveEnergyGap,show (0 : ℤ)<(n : ℤ) by exact_mod_cast n.pos,
    if_true,Int.toNat_natCast]

/-- Exact physical factorization of EVERY positive original energy gap,
including first and collapsed gaps, at an actual outside-spectrum lift. -/
theorem hillHminusPositiveEnergyGap_eq_miura_endpoint_sum_mul
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ))≠0) (n : ℕ+) :
    hillHminusPositiveEnergyGap q hr (n : ℤ)=
      (((hillMiuraDiracLeft u.val n).re+(hillMiuraDiracRight u.val n).re : ℝ) : ℂ)*
        (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n) := by
  obtain ⟨hL,hR⟩ := hillHminusLabels_pair_eq_squared_miuraDirac q hr u c hi hc n n.pos
  obtain ⟨hLi,hRi⟩ := hillMiuraDiracPair_real u (n : ℤ)
  have hLeft : hillMiuraDiracLeft u.val n=((hillMiuraDiracLeft u.val n).re : ℂ) :=
    Complex.ext rfl (by simp only [ofReal_im];exact hLi)
  have hRight : hillMiuraDiracRight u.val n=((hillMiuraDiracRight u.val n).re : ℂ) :=
    Complex.ext rfl (by simp only [ofReal_im];exact hRi)
  rw [hillHminusPositiveEnergyGap_apply_nat,hL,hR,hLeft,hRight]
  simp only [ofReal_re]
  push_cast
  ring

/-- One pair of constants controls EVERY Sobolev order and positive mode
of the ORIGINAL energy gaps against the actual weighted Dirac gaps. -/
theorem exists_hillHminus_energy_gap_weighted_norm_comparison
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ))≠0) :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ s : ℝ, ∀ n : ℕ+,
      A*‖(Weight.sobolev (s+1) (n : ℤ) : ℂ)*
        (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)‖ ≤
          ‖(Weight.sobolev s (n : ℤ) : ℂ)*hillHminusPositiveEnergyGap q hr (n : ℤ)‖ ∧
      ‖(Weight.sobolev s (n : ℤ) : ℂ)*hillHminusPositiveEnergyGap q hr (n : ℤ)‖ ≤
        B*‖(Weight.sobolev (s+1) (n : ℤ) : ℂ)*
          (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)‖ := by
  obtain ⟨A,B,hA,hB,hbound⟩ := exists_hillMiura_positive_endpoint_sum_linear_bounds u
  have hb (n : ℕ+) : A*(1+(n : ℝ))≤
      (hillMiuraDiracLeft u.val n).re+(hillMiuraDiracRight u.val n).re ∧
      (hillMiuraDiracLeft u.val n).re+(hillMiuraDiracRight u.val n).re≤B*(1+(n : ℝ)) := by
    rcases n with ⟨n,hn⟩
    cases n with
    | zero => omega
    | succ k =>
      change A*(1+((k+1 : ℕ) : ℝ))≤
        (hillMiuraDiracLeft u.val ((k+1 : ℕ) : ℤ)).re+
          (hillMiuraDiracRight u.val ((k+1 : ℕ) : ℤ)).re ∧
        (hillMiuraDiracLeft u.val ((k+1 : ℕ) : ℤ)).re+
          (hillMiuraDiracRight u.val ((k+1 : ℕ) : ℤ)).re≤B*(1+((k+1 : ℕ) : ℝ))
      have H := hbound k
      have he : (k : ℝ)+2=1+((k+1 : ℕ) : ℝ) := by push_cast;ring
      simpa only [he,Nat.cast_add,Nat.cast_one] using H
  refine ⟨A,B,hA,hB,?_⟩
  intro s n
  let τ : ℝ := (hillMiuraDiracLeft u.val n).re+(hillMiuraDiracRight u.val n).re
  have hτ : 0<τ := lt_of_lt_of_le (by positivity : 0<A*(1+(n : ℝ))) (hb n).1
  have hw : Weight.sobolev (s+1) (n : ℤ)=Weight.sobolev s (n : ℤ)*(1+(n : ℝ)) := by
    rw [Weight.sobolev_add]
    simp only [Weight.sobolev_apply 1,Int.cast_natCast,Real.rpow_one,
      abs_of_nonneg (by positivity : (0 : ℝ)≤n)]
  have hH : ‖(Weight.sobolev s (n : ℤ) : ℂ)*hillHminusPositiveEnergyGap q hr (n : ℤ)‖=
      τ*(Weight.sobolev s (n : ℤ)*‖hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n‖) := by
    rw [hillHminusPositiveEnergyGap_eq_miura_endpoint_sum_mul q hr u c hi hc n]
    change ‖(Weight.sobolev s (n : ℤ) : ℂ)*((τ : ℂ)*_)‖=_
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hτ,
      abs_of_pos (Weight.positive _ _)]
    ring
  have hD : ‖(Weight.sobolev (s+1) (n : ℤ) : ℂ)*
      (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)‖=
      (1+(n : ℝ))*(Weight.sobolev s (n : ℤ)*
        ‖hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n‖) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Weight.positive _ _),hw]
    ring
  rw [hH,hD]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb n).1
      (mul_nonneg (Weight.positive _ _).le (norm_nonneg _))
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb n).2
      (mul_nonneg (Weight.positive _ _).le (norm_nonneg _))

/-- The exact native weighted membership equivalence for the ORIGINAL
positive Hill energy gaps and full signed actual Dirac gaps. -/
theorem hillHminus_energy_gap_mem_iff_miura_Dirac_gap_mem
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ))≠0) (s : ℝ) :
    Memℓp (fun n : ℤ => (Weight.sobolev s n : ℂ)*hillHminusPositiveEnergyGap q hr n) 2 ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (s+1) n : ℂ)*
        (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)) 2 := by
  let D (n : ℤ) := (Weight.sobolev (s+1) n : ℂ)*
    (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)
  have hneg (n : ℤ) : D (-n)=D n := by
    obtain ⟨hL,hR⟩ := hillMiuraCanonicalEndpoints_neg u.val n
    change (Weight.sobolev (s+1) (-n) : ℂ)*
      (hillMiuraDiracRight u.val (-n)-hillMiuraDiracLeft u.val (-n))=_
    change hillMiuraDiracLeft u.val (-n)= -hillMiuraDiracRight u.val n at hL
    change hillMiuraDiracRight u.val (-n)= -hillMiuraDiracLeft u.val n at hR
    rw [Weight.sobolev_neg,hL,hR]
    dsimp only [D]
    ring
  have heven := memlp_iff_positive_half_of_norm_neg_eq (p := 2) D (fun n => congrArg norm (hneg n))
  rw [heven]
  obtain ⟨A,B,hA,_hB,hbound⟩ := exists_hillHminus_energy_gap_weighted_norm_comparison q hr u c hi hc
  have hnorm (j : ℤ) :
      A*‖if 0<j then D j else 0‖≤‖(Weight.sobolev s j : ℂ)*hillHminusPositiveEnergyGap q hr j‖ ∧
      ‖(Weight.sobolev s j : ℂ)*hillHminusPositiveEnergyGap q hr j‖≤B*‖if 0<j then D j else 0‖ := by
    by_cases hj : 0<j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have hn : (n : ℤ)=j := Int.toNat_of_nonneg hj.le
      simpa only [hn,if_pos hj,D] using hbound s n
    · simp only [hillHminusPositiveEnergyGap,if_neg hj,mul_zero,norm_zero,mul_zero,le_refl,and_self]
  constructor
  · intro hH
    apply (hH.norm.const_mul (1/A)).mono
    intro j
    have h := (hnorm j).1
    exact (le_div_iff₀ hA).mpr (by nlinarith) |>.trans_eq (by rw [div_eq_mul_inv];ring)
  · intro hD
    apply (hD.norm.const_mul B).mono
    exact fun j => (hnorm j).2

/-- EVERY real rough Hill source has H^s coefficients exactly when its
ORIGINAL positive energy gaps have native weight H^s, for ALL s>=-1. -/
theorem hillHminus_sobolev_mem_iff_original_energy_gap_mem
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (s : ℝ) (hs : -1≤s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 ↔
      Memℓp (fun n : ℤ => (Weight.sobolev s n : ℂ)*hillHminusPositiveEnergyGap q hr n) 2 := by
  obtain ⟨C,c,_hc,hshift,hq,hreal,houtside⟩ := exists_hillHminus_outside_real_Miura_chart q hr
  let u : PeriodOneRealL2 := ⟨C.lift q,(periodOneL2Conjugation_fixed_iff _).mp (hreal q hq hr)⟩
  have hi : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    simpa only [u,hshift,Complex.ofReal_pow] using C.image q hq
  have ho : hillHminusRadicand q (-((c^2 : ℝ) : ℂ))≠0 := by
    simpa only [hshift,Complex.ofReal_pow] using houtside q hq
  exact (hillHminus_sobolev_iff_real_miuraDirac_gap_mem q u ((c^2 : ℝ) : ℂ) hi s hs).trans
    (hillHminus_energy_gap_mem_iff_miura_Dirac_gap_mem q hr u (c^2) hi ho s).symm

end NLS.KdV
