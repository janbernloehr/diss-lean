import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.SequenceSpaces.OrderedNatEnumerationUnique
import NLS.KdV.HillMiuraSquaredEnumeration

/-! # Every original Hill label is the corresponding squared Miura label

Both actual complete natural enumerations have the same full algebraic
multiplicities. Ordered-enumeration uniqueness identifies ALL slots,
including the bottom and every repeated low or collapsed positive pair.
The only additional shift condition is a proved outside-spectrum energy.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusLabels_eq_squared_miuraDirac
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ)) ≠ 0) :
    hillHminusRealLabels q hq = hillMiuraSquaredLabels u.val c := by
  apply ordered_nat_enumeration_eq_of_multiplicity
    (hillHminusRealLabels q hq) (hillMiuraSquaredLabels u.val c)
    (finite_fiber_hillHminusRealLabels q hq) (hillMiuraSquaredLabels_finite_fiber u c)
    (monotone_hillHminusRealLabels q hq) (monotone_hillMiuraSquaredLabels u c)
  intro x
  rw [multiplicity_hillHminusRealLabels q hq x,
    hillMiuraSquaredLabels_global_multiplicity q hq u c himage hc x]

theorem hillHminusLabels_bottom_eq_squared_miuraDirac
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ)) ≠ 0) :
    hillHminusRealLabels q hq 0 = (hillMiuraDiracRight u.val 0).re^2-c := by
  have h := congrFun (hillHminusLabels_eq_squared_miuraDirac q hq u c himage hc) 0
  simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_initial] using h

theorem hillHminusLabels_pair_eq_squared_miuraDirac
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ)) ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    hillHminusRealLabels q hq (2*n-1) = (hillMiuraDiracLeft u.val n).re^2-c ∧
      hillHminusRealLabels q hq (2*n) = (hillMiuraDiracRight u.val n).re^2-c := by
  have he := hillHminusLabels_eq_squared_miuraDirac q hq u c himage hc
  constructor
  · simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left u.val n hn] using congrFun he (2*n-1)
  · simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right u.val n hn] using congrFun he (2*n)

theorem hillHminusLabels_bottom_lt_first
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ)) ≠ 0) :
    hillHminusRealLabels q hq 0 < hillHminusRealLabels q hq 1 := by
  have hbot := hillHminusLabels_bottom_eq_squared_miuraDirac q hq u c himage hc
  have hfirst := (hillHminusLabels_pair_eq_squared_miuraDirac q hq u c himage hc 1 (by norm_num)).1
  norm_num at hfirst
  rw [hbot,hfirst]
  have hsep := hillMiuraDirac_re_separated u (show (0 : ℤ) < 1 by norm_num)
  have hnonneg := (hillMiura_gap_zero_contains_zero u).2
  change 0 ≤ (hillMiuraDiracRight u.val 0).re at hnonneg
  nlinarith

theorem hillHminusLabels_bottom_multiplicity_one
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ)) ≠ 0) :
    analyticOrderNatAt (hillHminusRadicand q) (hillHminusRealLabels q hq 0 : ℂ) = 1 := by
  rw [← multiplicity_hillHminusRealLabels q hq]
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    have hlt := (hillHminusLabels_bottom_lt_first q hq u c himage hc).trans_le
      (monotone_hillHminusRealLabels q hq (show 1 ≤ j by omega))
    exact if_neg hlt.ne'

end NLS.KdV
