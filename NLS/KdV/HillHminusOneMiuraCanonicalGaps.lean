import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.KdV.HillHminusOneMiuraPositiveIndexedActions

/-! # Miura action zero detection uses the original Hill gap at every index

The full label identification retains the difference-of-squares factor.
Strict positivity of the Dirac endpoints makes its sum factor nonzero,
so the constructed real Miura action vanishes exactly when the ORIGINAL
Hill gap closes, at every positive index including the low cluster.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat

theorem hillHminus_gap_eq_miuraDirac_product
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (n : ℕ) (hn : 0 < n) :
    ((hillHminusLabels q hq (2*n)-hillHminusLabels q hq (2*n-1) : ℝ) : ℂ) =
      (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)*
        (hillMiuraDiracRight u.val n+hillMiuraDiracLeft u.val n) := by
  obtain ⟨hl,hr⟩ := hillHminusLabels_pair_eq_squared_miuraDirac q hq u c himage hc n hn
  have him := hillMiuraDiracPair_real u n
  have hL : ((hillMiuraDiracLeft u.val n).re : ℂ) = hillMiuraDiracLeft u.val n :=
    Complex.ext rfl him.1.symm
  have hR : ((hillMiuraDiracRight u.val n).re : ℂ) = hillMiuraDiracRight u.val n :=
    Complex.ext rfl him.2.symm
  rw [hl,hr]
  push_cast
  rw [hL,hR]
  ring

theorem hillHminus_gap_eq_zero_iff_miuraDirac_gap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (n : ℕ) (hn : 0 < n) :
    ((hillHminusLabels q hq (2*n)-hillHminusLabels q hq (2*n-1) : ℝ) : ℂ) = 0 ↔
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n = 0 := by
  have hpos := hillMiura_positive_gap_left_pos u n (by exact_mod_cast hn)
  change 0 < (hillMiuraDiracLeft u.val n).re at hpos
  have hord := hillMiuraDiracPair_ordered u.val n
  have hsum : hillMiuraDiracRight u.val n+hillMiuraDiracLeft u.val n ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [add_re,zero_re] at hr
    linarith
  rw [hillHminus_gap_eq_miuraDirac_product q hq u c himage hc n hn,mul_eq_zero,or_iff_left hsum]
  rfl

theorem hillHminusMiuraIndexedAction_eq_zero_iff_Hill_gap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (n : ℕ) (hn : 0 < n) :
    hillHminusMiuraIndexedAction u.val n = 0 ↔
      ((hillHminusLabels q hq (2*n)-hillHminusLabels q hq (2*n-1) : ℝ) : ℂ) = 0 := by
  exact (hillHminusMiuraIndexedAction_positive_index_spec u n (by exact_mod_cast hn)).2.2.trans
    (hillHminus_gap_eq_zero_iff_miuraDirac_gap q hq u c himage hc n hn).symm

theorem hillHminusMiuraIndexedAction_pos_iff_Hill_gap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (n : ℕ) (hn : 0 < n) :
    0 < (hillHminusMiuraIndexedAction u.val n).re ↔
      ((hillHminusLabels q hq (2*n)-hillHminusLabels q hq (2*n-1) : ℝ) : ℂ) ≠ 0 := by
  exact (hillHminusMiuraIndexedAction_positive_index_pos_iff u n (by exact_mod_cast hn)).trans
    (not_congr (hillHminus_gap_eq_zero_iff_miuraDirac_gap q hq u c himage hc n hn)).symm

end NLS.KdV
