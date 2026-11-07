import NLS.Articles.KdVPseudomeasures.OriginalHillAnalyticAbelianCorrection
import NLS.KdV.HillAbelianUniformExponentialBound

/-! The ACTUAL correction is analytic and locally bounded uniformly
in ALL n on ONE common complex native neighborhood. The whole sequence
is analytic into l-infinity. These are the correction estimates needed
for Section5; the action amplitude/full coordinates remain separate. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_uniform_Abelian_correction_common_domain :
    IsOpen hillHminusOffIndexBoundedDomain ∧ IsConnected hillHminusOffIndexBoundedDomain ∧
      hillHminusOffIndexBoundedDomain ⊆ hillHminusOffIndexAnalyticDomain ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusOffIndexBoundedDomain) ∧
      AnalyticOnNhd ℂ hillHminusOffIndexAbelianBoundedSequence hillHminusOffIndexBoundedDomain :=
  ⟨isOpen_hillHminusOffIndexBoundedDomain,isConnected_hillHminusOffIndexBoundedDomain,
    hillHminusOffIndexBoundedDomain_subset_analytic,
    (fun q => real_mem_hillHminusOffIndexBoundedDomain _ (originalPeriodOneCoefficients_real q)),
    analyticOnNhd_hillHminusOffIndexAbelianBoundedSequence⟩

theorem original_Hill_infinite_correction_UNIFORM_ALL_n_bound :
    ∀ q ∈ hillHminusOffIndexBoundedDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusOffIndexBoundedDomain ∧
      ∃ R : ℝ, 0 < R ∧ ∀ a ∈ U, ∀ n : ℕ+,
        (∑' m : ℕ+, ‖hillHminusOffIndexAbelianTerm n a m‖) ≤ R ∧
          ‖hillHminusOffIndexAbelianCorrection n a‖ ≤ R :=
  exists_locally_uniform_hillHminusOffIndexAbelianCorrection_bound

theorem original_Hill_infinite_phase_multiplier_UNIFORM_ALL_n_bound :
    ∀ q ∈ hillHminusOffIndexBoundedDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusOffIndexBoundedDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖Complex.exp (I*hillHminusOffIndexAbelianCorrection n a)‖ ≤ C ∧
          ‖Complex.exp (-I*hillHminusOffIndexAbelianCorrection n a)‖ ≤ C :=
  exists_local_uniform_offIndex_phase_exponential_bound

theorem original_Hill_complete_Abelian_UNIFORM_diagonal_multiplier_bound :
    ∀ q ∈ hillHminusOffIndexBoundedDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusOffIndexBoundedDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖hillHminusAbelianCartesianPlus n a‖ ≤ C*‖hillHminusDiagonalCartesianPlus n a‖ ∧
          ‖hillHminusAbelianCartesianMinus n a‖ ≤ C*‖hillHminusDiagonalCartesianMinus n a‖ :=
  exists_local_uniform_complete_Abelian_diagonal_multiplier_bound

end NLS.Articles.KdVPseudomeasures
