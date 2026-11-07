import NLS.Articles.KdVPseudomeasures.OriginalHillUniformZeroSequenceBounds
import NLS.KdV.HillUniformEnergyGapOffsetDomain

/-! The ACTUAL original Hill zero estimate O(gamma_m^2/m) on ONE open
connected complex native neighborhood of ENTIRE real Hminus-one,
locally uniformly at EVERY complex source and before ALL numerator and
gap indices. Original energy midpoints, gaps and indices are retained. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_common_complex_fine_zero_offset_domain :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ IsConnected U ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ U) ∧
      U ⊆ hillHminusCanonicalZeroSequenceDomain ∩ hillHminusCanonicalGapDomain ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalZeroSequence n) U) ∧
      (∀ m : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalEnergyMidpoint m) U) ∧
      ∀ q ∈ U, ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ball q r ⊆ U ∧
        ∀ y ∈ ball q r, ∀ n m : ℕ+,
          ‖hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n y)-hillHminusCanonicalEnergyMidpoint m y‖ ≤
            C*‖hillHminusCanonicalGapSquare m y‖/(m:ℝ) := by
  refine ⟨hillHminusFineZeroSequenceDomain,isOpen_hillHminusFineZeroSequenceDomain,
    isConnected_hillHminusFineZeroSequenceDomain,
    (fun q => real_mem_hillHminusFineZeroSequenceDomain _ (originalPeriodOneCoefficients_real q)),
    hillHminusFineZeroSequenceDomain_subset,
    (fun n => (analyticOnNhd_hillHminusCanonicalZeroSequence n).mono
      (hillHminusFineZeroSequenceDomain_subset.trans inter_subset_left)),
    (fun m => (analyticOnNhd_hillHminusCanonicalEnergyMidpoint m).mono
      (hillHminusFineZeroSequenceDomain_subset.trans inter_subset_left)),
    exists_locally_uniform_hillHminus_zero_squared_energy_gap_offset⟩

theorem original_Hill_real_fine_zero_offset_bound (q : OriginalHminusOnePotential) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ p : OriginalHminusOnePotential, originalPeriodOneCoefficients p ∈ ball (originalPeriodOneCoefficients q) r →
        ∀ n m : ℕ+,
          ‖(originalHillPsiRealZero n m p:ℂ)-
            ((hillHminusLabels (originalPeriodOneCoefficients p) (originalPeriodOneCoefficients_real p) (2*(m:ℕ)-1):ℂ)+
              (hillHminusLabels (originalPeriodOneCoefficients p) (originalPeriodOneCoefficients_real p) (2*(m:ℕ)):ℂ))/2‖ ≤
            C*‖((hillHminusLabels (originalPeriodOneCoefficients p) (originalPeriodOneCoefficients_real p) (2*(m:ℕ)):ℂ)-
              (hillHminusLabels (originalPeriodOneCoefficients p) (originalPeriodOneCoefficients_real p) (2*(m:ℕ)-1):ℂ))^2‖/(m:ℝ) := by
  obtain ⟨r,C,hr,hC,_,hbound⟩ := exists_locally_uniform_hillHminus_zero_squared_energy_gap_offset
    (originalPeriodOneCoefficients q) (real_mem_hillHminusFineZeroSequenceDomain _ (originalPeriodOneCoefficients_real q))
  refine ⟨r,C,hr,hC,?_⟩
  intro p hp n m
  have h := hbound (originalPeriodOneCoefficients p) hp n m
  rw [hillHminusCanonicalZeroSequence_real n _ (originalPeriodOneCoefficients_real p),hillEnergySequenceZero_real,
    hillHminusCanonicalEnergyMidpoint_real m _ (originalPeriodOneCoefficients_real p),
    hillHminusCanonicalGapSquare_eq_real _ (originalPeriodOneCoefficients_real p) m] at h
  exact h

theorem original_Hill_filled_energy_midpoint_analytic (m : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalEnergyMidpoint m) hillHminusFineZeroSequenceDomain ∧
      ∀ q : OriginalHminusOnePotential,
        hillHminusCanonicalEnergyMidpoint m (originalPeriodOneCoefficients q) =
          ((hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) (2*(m:ℕ)-1):ℂ)+
            (hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) (2*(m:ℕ)):ℂ))/2 :=
  ⟨(analyticOnNhd_hillHminusCanonicalEnergyMidpoint m).mono
    (hillHminusFineZeroSequenceDomain_subset.trans inter_subset_left),
    fun q => hillHminusCanonicalEnergyMidpoint_real m _ (originalPeriodOneCoefficients_real q)⟩

end NLS.Articles.KdVPseudomeasures
