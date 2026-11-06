import NLS.KdV.HillMiuraGroundEnumeration
import NLS.KdV.HillHminusOneMiuraAllLabels

/-! # All canonical Hill slots at the actual normalized ground factor

The complete squared enumeration includes the single simple ground
energy. Ordered multiplicity uniqueness identifies every low and high
slot, including every collapsed positive pair, at the critical factor.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusLabels_eq_squared_miuraDirac_of_meanZero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hm : u.val 0 = 0) :
    hillHminusRealLabels q hq = hillMiuraSquaredLabels u.val c := by
  apply ordered_nat_enumeration_eq_of_multiplicity
    (hillHminusRealLabels q hq) (hillMiuraSquaredLabels u.val c)
    (finite_fiber_hillHminusRealLabels q hq) (hillMiuraSquaredLabels_finite_fiber u c)
    (monotone_hillHminusRealLabels q hq) (monotone_hillMiuraSquaredLabels u c)
  intro x
  rw [multiplicity_hillHminusRealLabels q hq x,
    hillMiuraSquaredLabels_global_multiplicity_of_meanZero q hq u c himage hm x]

theorem hillHminusLabels_bottom_eq_squared_miuraDirac_of_meanZero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hm : u.val 0 = 0) :
    hillHminusRealLabels q hq 0 = (hillMiuraDiracRight u.val 0).re^2-c := by
  have h := congrFun (hillHminusLabels_eq_squared_miuraDirac_of_meanZero q hq u c himage hm) 0
  simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_initial] using h

theorem hillHminusLabels_pair_eq_squared_miuraDirac_of_meanZero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hm : u.val 0 = 0)
    (n : ℕ) (hn : 0 < n) :
    hillHminusRealLabels q hq (2*n-1) = (hillMiuraDiracLeft u.val n).re^2-c ∧
      hillHminusRealLabels q hq (2*n) = (hillMiuraDiracRight u.val n).re^2-c := by
  have he := hillHminusLabels_eq_squared_miuraDirac_of_meanZero q hq u c himage hm
  constructor
  · simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left u.val n hn] using congrFun he (2*n-1)
  · simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right u.val n hn] using congrFun he (2*n)


end NLS.KdV
