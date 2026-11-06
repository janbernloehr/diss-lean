import NLS.Articles.KdVConvexity.GlobalArnoldCalibration
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughGroundEnergyBound

/-! # Global intrinsic rough energy and source bounds in the original Arnold norm -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

/-- Every actual analytic Arnold-action realization obeys the global
intrinsic ground-energy bound, including every real non-L2 source. -/
theorem ground_energy_le_global_Arnold_norm
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q} ⊆ Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    -hillHminusLowestRealRoot q hr ≤ (2/Real.pi)*‖I q‖ := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  have h := D.ground_energy_le_positive_norm q hr hm
  rwa [←global_Arnold_norm_eq_positive_norm_sq D Ω hΩ I hI hrec q hr] at h

/-- Fixed universal operator constants control the actual rough source
by its original weighted Arnold-action norm. -/
theorem source_norm_le_global_Arnold_norm
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q} ⊆ Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    ‖q‖ ≤ (‖periodOneMassOperator 0‖+‖periodOneL2Inclusion‖)*
        Real.sqrt ((2/Real.pi)*‖I q‖)+
      (‖periodOneMiuraProduct‖+‖periodOneL2Inclusion‖)*((2/Real.pi)*‖I q‖) := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  have h := D.norm_source_le_positive_norm q hr hm
  rwa [←global_Arnold_norm_eq_positive_norm_sq D Ω hΩ I hI hrec q hr] at h

/-- The actual analytic weighted Arnold map exists on a neighborhood of
all real rough potentials and satisfies the global mean-zero energy and
source estimates. No finite-gap or initial size premise remains. -/
theorem exists_global_analytic_Arnold_map_with_coercivity :
    ∃ Ω : Set PeriodOneHminusOne, ∃ I : PeriodOneHminusOne → BaseActionSpace,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧ AnalyticOnNhd ℂ I Ω ∧
      (∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
        (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0) ∧
      (∀ q, IsRealPeriodOneHminusOne q → I q ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1) ∧
      ∀ q (hr : IsRealPeriodOneHminusOne q), q.val 0 = 0 →
        -hillHminusLowestRealRoot q hr ≤ (2/Real.pi)*‖I q‖ ∧
        ‖q‖ ≤ (‖periodOneMassOperator 0‖+‖periodOneL2Inclusion‖)*
            Real.sqrt ((2/Real.pi)*‖I q‖)+
          (‖periodOneMiuraProduct‖+‖periodOneL2Inclusion‖)*((2/Real.pi)*‖I q‖) := by
  obtain ⟨Ω,I,hΩ,hreal,hI,hrec,hpos,_hzero,_hI0,_hinv⟩ :=
    exists_global_analytic_weighted_Arnold_action_map
  refine ⟨Ω,I,hΩ,hreal,hI,hrec,hpos,?_⟩
  intro q hr hm
  exact ⟨ground_energy_le_global_Arnold_norm Ω hreal I hI hrec q hr hm,
    source_norm_le_global_Arnold_norm Ω hreal I hI hrec q hr hm⟩

end NLS.Articles.KdVConvexity
