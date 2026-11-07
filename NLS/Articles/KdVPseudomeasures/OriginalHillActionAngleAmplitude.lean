import NLS.Articles.KdVPseudomeasures.OriginalHillUniformAbelianCorrection
import NLS.KdV.HillActionAngleUniformBound

/-! Section 5 scalar action-angle construction with the ACTUAL Hill
spectra, AUXILIARY divisor, physical sheet and entire Abelian phase.
The positive normalized-action amplitude is now included. Sequence
regularity, Gardner canonicality and the main theorems remain open. -/
noncomputable section
open Set Complex NLS.KdV
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_action_amplitude_common_domain :
    IsOpen hillHminusActionAmplitudeDomain ∧ IsConnected hillHminusActionAmplitudeDomain ∧
      hillHminusActionAmplitudeDomain ⊆ hillHminusCanonicalRatioDomain ∧
      hillHminusActionAmplitudeDomain ⊆ hillHminusOffIndexBoundedDomain ∧
      (∀ q : OriginalHminusOnePotential,
        originalPeriodOneCoefficients q ∈ hillHminusActionAmplitudeDomain) ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalActionAmplitude n) hillHminusActionAmplitudeDomain ∧
        AnalyticOnNhd ℂ (hillHminusActionAngleX n) hillHminusActionAmplitudeDomain ∧
        AnalyticOnNhd ℂ (hillHminusActionAngleY n) hillHminusActionAmplitudeDomain) :=
  ⟨isOpen_hillHminusActionAmplitudeDomain,isConnected_hillHminusActionAmplitudeDomain,
    hillHminusActionAmplitudeDomain_subset_ratio,hillHminusActionAmplitudeDomain_subset_bounded,
    (fun q => real_mem_hillHminusActionAmplitudeDomain _ (originalPeriodOneCoefficients_real q)),
    (fun n => ⟨analyticOnNhd_hillHminusCanonicalActionAmplitude n,
      analyticOnNhd_hillHminusActionAngleX n,analyticOnNhd_hillHminusActionAngleY n⟩)⟩

theorem original_Hill_action_amplitude_positive_real (q : OriginalHminusOnePotential) (n : ℕ+) :
    (hillHminusCanonicalActionAmplitude n (originalPeriodOneCoefficients q)).im = 0 ∧
      0 < (hillHminusCanonicalActionAmplitude n (originalPeriodOneCoefficients q)).re :=
  hillHminusCanonicalActionAmplitude_real_positive n _ (originalPeriodOneCoefficients_real q)

theorem original_Hill_scalar_action_angle_identity (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) (n : ℕ+) :
    hillHminusActionAngleFactorPlus n q*hillHminusActionAngleFactorMinus n q = 2*hillHminusCanonicalAction n q ∧
      (hillHminusActionAngleX n q)^2+(hillHminusActionAngleY n q)^2 = 2*hillHminusCanonicalAction n q :=
  ⟨hillHminusActionAngleFactor_product n q hq,hillHminusActionAngle_sum_squares n q hq⟩

theorem original_Hill_scalar_action_angle_real_closed_gap (q : OriginalHminusOnePotential) (n : ℕ+) :
    (hillHminusActionAngleX n (originalPeriodOneCoefficients q)).im = 0 ∧
      (hillHminusActionAngleY n (originalPeriodOneCoefficients q)).im = 0 ∧
      (hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) = 0 →
        hillHminusActionAngleX n (originalPeriodOneCoefficients q) = 0 ∧
          hillHminusActionAngleY n (originalPeriodOneCoefficients q) = 0) :=
  ⟨(hillHminusActionAngle_real n _ (originalPeriodOneCoefficients_real q)).1,
    (hillHminusActionAngle_real n _ (originalPeriodOneCoefficients_real q)).2,
    hillHminusActionAngle_zero_of_real_closed_gap n _ (originalPeriodOneCoefficients_real q)⟩

theorem original_Hill_action_amplitude_UNIFORM_ALL_n_bound :
    ∀ q ∈ hillHminusActionAmplitudeDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAmplitudeDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖hillHminusCanonicalActionAmplitude n a‖ ≤ C/Real.sqrt (n:ℕ) :=
  exists_local_uniform_hillHminusCanonicalActionAmplitude_bound

theorem original_Hill_action_angle_UNIFORM_diagonal_bound :
    ∀ q ∈ hillHminusActionAmplitudeDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAmplitudeDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖hillHminusActionAngleFactorPlus n a‖ ≤
          (C/Real.sqrt (n:ℕ))*‖hillHminusDiagonalCartesianPlus n a‖ ∧
        ‖hillHminusActionAngleFactorMinus n a‖ ≤
          (C/Real.sqrt (n:ℕ))*‖hillHminusDiagonalCartesianMinus n a‖ :=
  exists_local_uniform_actionAngle_diagonal_bound

end NLS.Articles.KdVPseudomeasures
