import NLS.KdV.HillHminusOnePhysicalGroundMultiplicity
import NLS.KdV.HillHminusOnePhysicalGapMultiplicity

/-! # Actual original Hill algebraic multiplicity equals characteristic order

For every real unit-period H^-1 potential and every complex energy, the
full original H1-domain algebraic root-space dimension is exactly the
finite analytic zero order of the actual entire characteristic. This
includes the ground value, open gaps, closed gaps and nonspectral points.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem singularHillAlgebraicMultiplicity_periodOne_eq_analyticOrderNatAt
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (z : ℂ) :
    singularHillAlgebraicMultiplicity (periodOneSingularPotential q) z =
      analyticOrderNatAt (hillHminusRadicand q) z := by
  by_cases hz : hillHminusRadicand q z = 0
  · obtain ⟨j,rfl⟩ := (hillHminusRealLabels_root_iff q hr z).mp hz
    by_cases hj : j = 0
    · subst j
      have hp := hillHminusLowestRealRoot_physical_multiplicity_one q hr
      have ha := hillHminusLowestRealRoot_order_one q hr
      rw [← hillHminusRealLabels_zero_eq_lowest q hr] at hp ha
      exact hp.trans ha.symm
    · let n := (j+1)/2
      have hn : 1 ≤ n := by dsimp only [n]; omega
      have hcases : j = 2*n-1 ∨ j = 2*n := by dsimp only [n]; omega
      rcases hcases with h | h
      · exact hillHminusRealLabels_physical_pair_multiplicity q hr n hn _
          (Or.inl (congrArg (hillHminusRealLabels q hr) h))
      · exact hillHminusRealLabels_physical_pair_multiplicity q hr n hn _
          (Or.inr (congrArg (hillHminusRealLabels q hr) h))
  · have hp : singularHillAlgebraicMultiplicity (periodOneSingularPotential q) z = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hz ((periodOneSingularHillSpectrum_iff_characteristic q z).mp
        ((singularHillAlgebraicMultiplicity_pos_iff _ z).mp hpos))
    have ha : analyticOrderNatAt (hillHminusRadicand q) z = 0 := by
      simpa only [analyticOrderNatAt,ENat.toNat_zero] using
        congrArg ENat.toNat (analyticOrderAt_eq_zero.mpr (Or.inr hz))
    exact hp.trans ha.symm

theorem multiplicity_hillHminusRealLabels_physical
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    (∑ᶠ j : ℕ, if hillHminusRealLabels q hr j = x then (1 : ℕ) else 0) =
      singularHillAlgebraicMultiplicity (periodOneSingularPotential q) x := by
  rw [singularHillAlgebraicMultiplicity_periodOne_eq_analyticOrderNatAt q hr]
  exact multiplicity_hillHminusRealLabels q hr x

end NLS.KdV
