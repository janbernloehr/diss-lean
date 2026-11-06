import NLS.KdV.HillMiuraCriticalSpectrum
import NLS.SequenceSpaces.OrderedNatEnumerationUnique

/-! # Canonical Hill labels from the normalized ground-energy factor

This identification includes the ramified zero-frequency point and all
closed positive gaps. No shift outside the spectrum is required.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusRealLabels_eq_squared_critical_miura
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) :
    hillHminusRealLabels q hr = hillMiuraSquaredLabels u.val e := by
  apply ordered_nat_enumeration_eq_of_multiplicity _ _
    (finite_fiber_hillHminusRealLabels q hr) (hillMiuraSquaredLabels_finite_fiber u e)
    (monotone_hillHminusRealLabels q hr) (monotone_hillMiuraSquaredLabels u e)
  intro x
  rw [multiplicity_hillHminusRealLabels,
    hillMiuraSquaredLabels_critical_multiplicity q hr u e hm hi]

theorem hillHminusRealLabels_critical_miura_left
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (n : ℕ+) :
    hillHminusRealLabels q hr (2*(n : ℕ)-1) =
      (hillMiuraDiracLeft u.val (n : ℤ)).re^2-e := by
  rw [hillHminusRealLabels_eq_squared_critical_miura q hr u e hm hi,
    hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left u.val (n : ℕ) n.property]

theorem hillHminusRealLabels_critical_miura_right
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (n : ℕ+) :
    hillHminusRealLabels q hr (2*(n : ℕ)) =
      (hillMiuraDiracRight u.val (n : ℤ)).re^2-e := by
  rw [hillHminusRealLabels_eq_squared_critical_miura q hr u e hm hi,
    hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right u.val (n : ℕ) n.property]

end NLS.KdV
