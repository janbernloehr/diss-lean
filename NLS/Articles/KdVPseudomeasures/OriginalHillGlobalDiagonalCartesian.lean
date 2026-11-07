import NLS.Articles.KdVPseudomeasures.OriginalHillOnIndexAbelianPhase
import NLS.KdV.HillCanonicalDiagonalCartesian

/-! Intrinsic diagonal Hill gap-times-phase factors are globally
analytic on the SAME common complex source neighborhood as the actual
off-index Abelian family. These factors do not yet include the infinite
off-index phase sum or the normalized action-ratio amplitude. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_common_global_diagonal_and_offIndex_domain :
    IsOpen hillHminusPhysicalAbelianDomain ∧ IsConnected hillHminusPhysicalAbelianDomain ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusPhysicalAbelianDomain) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusDiagonalCartesianPlus n) hillHminusPhysicalAbelianDomain ∧
        AnalyticOnNhd ℂ (hillHminusDiagonalCartesianMinus n) hillHminusPhysicalAbelianDomain ∧
        ∀ m : ℕ+, m ≠ n → AnalyticOnNhd ℂ (hillHminusPhysicalOffIndexAbelianValue n m) hillHminusPhysicalAbelianDomain :=
  ⟨isOpen_hillHminusPhysicalAbelianDomain,isConnected_hillHminusPhysicalAbelianDomain,
    (fun q => real_mem_hillHminusPhysicalAbelianDomain _ (originalPeriodOneCoefficients_real q)),
    fun n => ⟨analyticOnNhd_hillHminusDiagonalCartesianPlus n,analyticOnNhd_hillHminusDiagonalCartesianMinus n,
      fun m hmn => analyticOnNhd_hillHminusPhysicalOffIndexAbelianValue n m hmn⟩⟩

theorem original_Hill_global_diagonal_factor_product :
    ∀ n : ℕ+, ∀ q ∈ hillHminusPhysicalAbelianDomain,
      hillHminusDiagonalCartesianPlus n q*hillHminusDiagonalCartesianMinus n q = hillHminusCanonicalGapSquare n q :=
  hillHminusDiagonalCartesian_product

theorem original_Hill_global_diagonal_zero_at_REAL_closed_gaps (n : ℕ+)
    (q : OriginalHminusOnePotential) (hg : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) = 0) :
    hillHminusDiagonalCartesianPlus n (originalPeriodOneCoefficients q) = 0 ∧
      hillHminusDiagonalCartesianMinus n (originalPeriodOneCoefficients q) = 0 :=
  hillHminusDiagonalCartesian_zero_of_real_closed_gap n _ (originalPeriodOneCoefficients_real q) hg

theorem original_Hill_global_onIndex_phase_mod_pi (n : ℕ+) :
    IsOpen {q | q ∈ hillHminusPhysicalAbelianDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0} ∧
      AnalyticOnNhd ℂ (hillHminusDiagonalPhaseSquare n)
        {q | q ∈ hillHminusPhysicalAbelianDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0} ∧
      ∀ q ∈ hillHminusPhysicalAbelianDomain, hillHminusCanonicalGapSquare n q ≠ 0 → hillHminusDiagonalPhaseSquare n q ≠ 0 :=
  ⟨isOpen_hillHminusDiagonalPhaseDomain n,analyticOnNhd_hillHminusDiagonalPhaseSquare n,hillHminusDiagonalPhaseSquare_ne_zero n⟩

theorem original_Hill_global_diagonal_matches_EVERY_real_patch (P : HillProductEquationPatch) (n : ℕ+)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) :
    hillHminusDiagonalCartesianPlus n (originalPeriodOneCoefficients q) = P.physicalOnIndexCartesianPlus n (originalPeriodOneCoefficients q) ∧
      hillHminusDiagonalCartesianMinus n (originalPeriodOneCoefficients q) = P.physicalOnIndexCartesianMinus n (originalPeriodOneCoefficients q) :=
  hillHminusDiagonalCartesian_eq_patch_of_real P n _ hq (originalPeriodOneCoefficients_real q)

theorem original_Hill_diagonal_WHOLE_complex_source_ball_overlap (B C : HillPhysicalAbelianSourceBall) :
    ∀ n : ℕ+, EqOn (B.diagonalPlus n) (C.diagonalPlus n) (B.source ∩ C.source) ∧
      EqOn (B.diagonalMinus n) (C.diagonalMinus n) (B.source ∩ C.source) :=
  fun n => ⟨B.diagonalPlus_eq_on_overlap C n,B.diagonalMinus_eq_on_overlap C n⟩

end NLS.Articles.KdVPseudomeasures
