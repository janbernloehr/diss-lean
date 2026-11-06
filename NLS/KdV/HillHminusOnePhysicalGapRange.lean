import NLS.KdV.HillHminusOnePhysicalGapProjection
import NLS.KdV.SingularHillProjectionRootPair
import NLS.KdV.SingularHillFreeMultiplicity

/-! # The physical canonical gap range has dimension two everywhere

The moving projection range contains exactly the two endpoint root
spaces. At zero this is the original free two-dimensional root space;
rank invariance retains dimension two through every closed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

theorem hillHminusPhysicalGapProjection_endpoints_mem
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    (hillHminusRealLabels q hr (2*n-1) : ℂ) ∈ ball (hillHminusRealGapCenter q hr n : ℂ)
      (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n) ∧
    (hillHminusRealLabels q hr (2*n) : ℂ) ∈ ball (hillHminusRealGapCenter q hr n : ℂ)
      (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n) := by
  obtain ⟨hd,hη,hl,hu,_⟩ := hillHminusRealGapContour_geometry q hr n hn
  constructor
  · rw [← hl,mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show hillHminusRealGapCenter q hr n-hillHminusRealGapHalfLength q hr n-
      hillHminusRealGapCenter q hr n = -hillHminusRealGapHalfLength q hr n by ring,
      abs_neg,abs_of_nonneg hd]
    linarith
  · rw [← hu,mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show hillHminusRealGapCenter q hr n+hillHminusRealGapHalfLength q hr n-
      hillHminusRealGapCenter q hr n = hillHminusRealGapHalfLength q hr n by ring,abs_of_nonneg hd]
    linarith

theorem hillHminusPhysicalGapProjection_only_endpoints
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ ball (hillHminusRealGapCenter q hr n : ℂ)
      (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n))
    (hzero : hillHminusRadicand q z = 0) :
    z = (hillHminusRealLabels q hr (2*n-1) : ℂ) ∨ z = (hillHminusRealLabels q hr (2*n) : ℂ) := by
  obtain ⟨_,hη,_,_,hsub⟩ := hillHminusRealGapContour_geometry q hr n hn
  have hcut : z ∈ segment ℝ (hillHminusRealLabels q hr (2*n-1) : ℂ) (hillHminusRealLabels q hr (2*n)) := by
    by_contra hnot
    apply hillHminusRadicand_ne_zero_on_realCutDomain q hr z (hsub ⟨?_,hnot⟩) hzero
    exact ball_subset_ball (by linarith) hz
  have hi := hillHminusRadicand_root_im_zero q hr z hzero
  have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
  have hx := re_mem_Icc_of_mem_real_segment _ _ (monotone_hillHminusRealLabels q hr (by omega)) z hcut
  have hp := (hillHminusRadicand_zero_on_gap_interval_iff q hr n hn z.re hx).mp (by rwa [he])
  rcases hp with hp | hp
  · exact Or.inl (he.symm.trans (congrArg ofReal hp))
  · exact Or.inr (he.symm.trans (congrArg ofReal hp))

theorem hillHminusPhysicalGapProjection_range
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    (hillHminusPhysicalGapProjection q hr n).range =
      singularHillRootSpaceTop (periodOneSingularPotential q) (hillHminusRealLabels q hr (2*n-1)) ⊔
      singularHillRootSpaceTop (periodOneSingularPotential q) (hillHminusRealLabels q hr (2*n)) := by
  obtain ⟨hl,hu⟩ := hillHminusPhysicalGapProjection_endpoints_mem q hr n hn
  exact singularHillRieszProjection_range_eq_pair _ (periodOneSingularPotential_real q hr) _ _
    (hillHminusPhysicalGapProjection_radius_pos q hr n hn) (hillHminusPhysicalGapProjection_resolvent q hr n hn)
    _ _ hl hu (fun z hz hspec => hillHminusPhysicalGapProjection_only_endpoints q hr n hn z hz
      ((periodOneSingularHillSpectrum_iff_characteristic q z).mp hspec))

theorem hillHminusPhysicalGapProjection_rank_zero (hr : IsRealPeriodOneHminusOne 0) (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℂ (hillHminusPhysicalGapProjection 0 hr n).range = 2 := by
  have hl : hillHminusRealLabels 0 hr (2*n-1) = freeHillValue n := by
    rw [hillHminusRealLabels_zero]
    congr 1
    omega
  have hu : hillHminusRealLabels 0 hr (2*n) = freeHillValue n := by
    rw [hillHminusRealLabels_zero]
    congr 1
    omega
  rw [hillHminusPhysicalGapProjection_range 0 hr n hn,hl,hu,sup_idem,map_zero]
  exact singularHillAlgebraicMultiplicity_zero_positive n hn

theorem hillHminusPhysicalGapProjection_rank_two
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℂ (hillHminusPhysicalGapProjection q hr n).range = 2 :=
  (hillHminusPhysicalGapProjection_rank_eq_zero q hr n hn).trans (hillHminusPhysicalGapProjection_rank_zero _ n hn)

end NLS.KdV
