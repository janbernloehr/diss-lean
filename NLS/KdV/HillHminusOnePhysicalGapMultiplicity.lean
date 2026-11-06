import NLS.KdV.HillHminusOnePhysicalGapRange

/-! # Exact original physical multiplicities at every real gap endpoint

A closed gap has one two-dimensional physical root space. An open gap
has two independent nonzero root spaces whose dimensions add to two.
Thus the original algebraic multiplicities match the scalar zero orders.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem hillHminusRealLabels_physical_closed_gap_multiplicity
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n)
    (hclosed : hillHminusRealLabels q hr (2*n-1) = hillHminusRealLabels q hr (2*n)) :
    singularHillAlgebraicMultiplicity (periodOneSingularPotential q) (hillHminusRealLabels q hr (2*n-1)) = 2 := by
  have hR := hillHminusPhysicalGapProjection_range q hr n hn
  rw [hclosed,sup_idem] at hR
  rw [hclosed]
  change Module.finrank ℂ (singularHillRootSpaceTop (periodOneSingularPotential q)
    (hillHminusRealLabels q hr (2*n) : ℂ)) = 2
  rw [← hR]
  exact hillHminusPhysicalGapProjection_rank_two q hr n hn

theorem hillHminusRealLabels_physical_open_gap_multiplicities
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n)
    (hopen : hillHminusRealLabels q hr (2*n-1) ≠ hillHminusRealLabels q hr (2*n)) :
    singularHillAlgebraicMultiplicity (periodOneSingularPotential q) (hillHminusRealLabels q hr (2*n-1)) = 1 ∧
    singularHillAlgebraicMultiplicity (periodOneSingularPotential q) (hillHminusRealLabels q hr (2*n)) = 1 := by
  obtain ⟨hl,hu⟩ := hillHminusPhysicalGapProjection_endpoints_mem q hr n hn
  have hne : (hillHminusRealLabels q hr (2*n-1) : ℂ) ≠ (hillHminusRealLabels q hr (2*n) : ℂ) :=
    fun he => hopen (Complex.ofReal_injective he)
  have hsum := singularHillRieszProjection_rank_eq_pair_multiplicity _ (periodOneSingularPotential_real q hr) _ _
    (hillHminusPhysicalGapProjection_radius_pos q hr n hn) (hillHminusPhysicalGapProjection_resolvent q hr n hn)
    _ _ hl hu hne (fun z hz hspec => hillHminusPhysicalGapProjection_only_endpoints q hr n hn z hz
      ((periodOneSingularHillSpectrum_iff_characteristic q z).mp hspec))
  change Module.finrank ℂ (hillHminusPhysicalGapProjection q hr n).range = _ at hsum
  rw [hillHminusPhysicalGapProjection_rank_two q hr n hn] at hsum
  have hpl := (singularHillAlgebraicMultiplicity_pos_iff (periodOneSingularPotential q) _).mpr
    ((hillHminusRealLabels_physical_spectrum_iff q hr _).mpr ⟨2*n-1,rfl⟩)
  have hpu := (singularHillAlgebraicMultiplicity_pos_iff (periodOneSingularPotential q) _).mpr
    ((hillHminusRealLabels_physical_spectrum_iff q hr _).mpr ⟨2*n,rfl⟩)
  omega

theorem hillHminusRealLabels_physical_pair_multiplicity
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x = hillHminusRealLabels q hr (2*n-1) ∨ x = hillHminusRealLabels q hr (2*n)) :
    singularHillAlgebraicMultiplicity (periodOneSingularPotential q) x =
      analyticOrderNatAt (hillHminusRadicand q) x := by
  by_cases hopen : hillHminusRealLabels q hr (2*n-1) ≠ hillHminusRealLabels q hr (2*n)
  · have hp := hillHminusRealLabels_physical_open_gap_multiplicities q hr n hn hopen
    have ha := hillHminusRealLabels_open_gap_orders q hr n hn hopen
    rcases hx with rfl | rfl
    · exact hp.1.trans ha.1.symm
    · exact hp.2.trans ha.2.symm
  · have hclosed := not_ne_iff.mp hopen
    have hp := hillHminusRealLabels_physical_closed_gap_multiplicity q hr n hn hclosed
    have ha := hillHminusRealLabels_closed_gap_order q hr n hn hclosed
    rcases hx with rfl | rfl
    · exact hp.trans ha.symm
    · rw [← hclosed]
      exact hp.trans ha.symm

end NLS.KdV
