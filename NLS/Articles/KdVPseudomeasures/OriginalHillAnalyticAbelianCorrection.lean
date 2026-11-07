import NLS.Articles.KdVPseudomeasures.OriginalHillOffIndexAbsoluteSum
import NLS.KdV.HillAbelianPhaseSquare
import NLS.KdV.HillAbelianPhysicalPhaseFormula

/-! The ACTUAL complete Abelian factors on one common native complex
neighborhood. The infinite correction is analytic; the factors include
its exponential and retain the original gap normalization. Uniform
all-n estimates and the action-ratio Birkhoff amplitude remain separate. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_complete_Abelian_analytic_common_domain :
    IsOpen hillHminusOffIndexAnalyticDomain ∧ IsConnected hillHminusOffIndexAnalyticDomain ∧
      hillHminusOffIndexAnalyticDomain ⊆ hillHminusOffIndexSummabilityDomain ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusOffIndexAnalyticDomain) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusOffIndexAbelianCorrection n) hillHminusOffIndexAnalyticDomain ∧
        AnalyticOnNhd ℂ (hillHminusAbelianCartesianPlus n) hillHminusOffIndexAnalyticDomain ∧
        AnalyticOnNhd ℂ (hillHminusAbelianCartesianMinus n) hillHminusOffIndexAnalyticDomain :=
  ⟨isOpen_hillHminusOffIndexAnalyticDomain,isConnected_hillHminusOffIndexAnalyticDomain,
    hillHminusOffIndexAnalyticDomain_subset_summability,
    (fun q => real_mem_hillHminusOffIndexAnalyticDomain _ (originalPeriodOneCoefficients_real q)),
    fun n => ⟨analyticOnNhd_hillHminusOffIndexAbelianCorrection n,
      analyticOnNhd_hillHminusAbelianCartesianPlus n,analyticOnNhd_hillHminusAbelianCartesianMinus n⟩⟩

theorem original_Hill_infinite_correction_locally_uniform_BEFORE_ALL_n :
    ∀ q ∈ hillHminusOffIndexAnalyticDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusOffIndexAnalyticDomain ∧
      ∀ n : ℕ+, TendstoUniformlyOn (hillHminusOffIndexAbelianPartialSum n)
        (hillHminusOffIndexAbelianCorrection n) atTop U :=
  exists_locally_uniform_hillHminusOffIndexAbelianCorrection

theorem original_Hill_complete_Abelian_factor_product :
    ∀ n : ℕ+, ∀ q ∈ hillHminusOffIndexAnalyticDomain,
      hillHminusAbelianCartesianPlus n q*hillHminusAbelianCartesianMinus n q = hillHminusCanonicalGapSquare n q :=
  hillHminusAbelianCartesian_product

theorem original_Hill_complete_Abelian_real_conjugacy (q : OriginalHminusOnePotential) :
    ∀ n : ℕ+, hillHminusAbelianCartesianMinus n (originalPeriodOneCoefficients q) =
      star (hillHminusAbelianCartesianPlus n (originalPeriodOneCoefficients q)) :=
  fun n => hillHminusAbelianCartesian_conjugate_of_real n _ (originalPeriodOneCoefficients_real q)

theorem original_Hill_complete_Abelian_original_gap_moduli (q : OriginalHminusOnePotential) :
    ∀ n : ℕ+,
      ‖hillHminusAbelianCartesianPlus n (originalPeriodOneCoefficients q)‖ =
        hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(n:ℕ))-
          hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(n:ℕ)-1) ∧
      ‖hillHminusAbelianCartesianMinus n (originalPeriodOneCoefficients q)‖ =
        hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(n:ℕ))-
          hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(n:ℕ)-1) :=
  fun n => norm_hillHminusAbelianCartesian_of_real n _ (originalPeriodOneCoefficients_real q)

theorem original_Hill_complete_Abelian_phase_mod_pi (n : ℕ+) :
    IsOpen {q | q ∈ hillHminusOffIndexAnalyticDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0} ∧
      AnalyticOnNhd ℂ (hillHminusAbelianPhaseSquare n)
        {q | q ∈ hillHminusOffIndexAnalyticDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0} ∧
      ∀ q ∈ hillHminusOffIndexAnalyticDomain, hillHminusCanonicalGapSquare n q ≠ 0 → hillHminusAbelianPhaseSquare n q ≠ 0 :=
  ⟨isOpen_hillHminusAbelianPhaseDomain n,analyticOnNhd_hillHminusAbelianPhaseSquare n,hillHminusAbelianPhaseSquare_ne_zero n⟩

end NLS.Articles.KdVPseudomeasures
