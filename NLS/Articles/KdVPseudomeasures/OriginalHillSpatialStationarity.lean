import NLS.KdV.HillSpatialTranslationDiscriminant
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCompactFibers
import NLS.Articles.KdVPseudomeasures.OriginalCanonicalActions
import NLS.Articles.KdVPseudomeasures.OriginalCanonicalGapSquares

/-! Actual spatial translation on the ENTIRE original physical mean-zero
Hminus-one Hill domain preserves the complete original spectrum, every
ordered label and every action. At L2 inputs the actual action differential
annihilates the physical2*pi spatial velocity in the Hminus-one norm. -/
noncomputable section
open Set Complex NLS.KdV Filter Topology
open scoped ComplexConjugate
namespace NLS.Articles.KdVPseudomeasures

/-- The same physically translated original distribution, retaining the
period-one raw Fourier phases and every original source constraint. -/
def originalHillSpatialTranslation (t : ℝ) (q : OriginalHminusOnePotential) : OriginalHminusOnePotential :=
  ⟨periodOneOriginal (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t
    (originalPeriodOneCoefficients q)),by
      apply (periodOneOriginal_source_iff _).mpr
      constructor
      · exact WeightedCoeff.spatialTranslation_real _ _ _ _ (originalPeriodOneCoefficients_real q)
      · rw [WeightedCoeff.spatialTranslation_apply,originalPeriodOneCoefficients_mean_zero,mul_zero]⟩

theorem originalHillSpatialTranslation_coefficients (t : ℝ) (q : OriginalHminusOnePotential) :
    originalPeriodOneCoefficients (originalHillSpatialTranslation t q)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t (originalPeriodOneCoefficients q) :=
  periodOneOriginalExtract_original _

theorem originalHillSpatialTranslation_zero (q : OriginalHminusOnePotential) :
    originalHillSpatialTranslation 0 q=q := by
  apply Subtype.ext
  exact (congrArg periodOneOriginal (WeightedCoeff.spatialTranslation_zero
    (Weight.sobolev (-1)) (2*Real.pi) (originalPeriodOneCoefficients q))).trans
      (periodOneOriginal_originalPeriodOneCoefficients q)

theorem originalHillSpatialTranslation_add (t s : ℝ) (q : OriginalHminusOnePotential) :
    originalHillSpatialTranslation t (originalHillSpatialTranslation s q)=originalHillSpatialTranslation (t+s) q := by
  have he : originalPeriodOneCoefficients (originalHillSpatialTranslation t (originalHillSpatialTranslation s q))=
      originalPeriodOneCoefficients (originalHillSpatialTranslation (t+s) q) := by
    rw [originalHillSpatialTranslation_coefficients,originalHillSpatialTranslation_coefficients,
      originalHillSpatialTranslation_coefficients,WeightedCoeff.spatialTranslation_add]
  apply Subtype.ext
  simpa only [periodOneOriginal_originalPeriodOneCoefficients] using congrArg periodOneOriginal he

/-- EVERY translation stays in the FULL original physical isospectral set,
including all algebraic multiplicities and all low or collapsed slots. -/
theorem originalHillSpatialTranslation_isospectral (t : ℝ) (q : OriginalHminusOnePotential) :
    originalHillSpatialTranslation t q ∈ originalIsospectralSet q := by
  apply (mem_originalIsospectralSet_iff_discriminant_eq q _).mpr
  funext E
  change hillHminusDiscriminant (originalPeriodOneCoefficients (originalHillSpatialTranslation t q)) E=
    hillHminusDiscriminant (originalPeriodOneCoefficients q) E
  rw [originalHillSpatialTranslation_coefficients,hillHminusDiscriminant_spatialTranslation]

theorem originalHillLabels_spatialTranslation (t : ℝ) (q : OriginalHminusOnePotential) :
    originalHillLabels (originalHillSpatialTranslation t q)=originalHillLabels q :=
  (mem_originalIsospectralSet_iff_originalHillLabels q _).mp (originalHillSpatialTranslation_isospectral t q)

theorem originalCanonicalGapValues_spatialTranslation (t : ℝ) (q : OriginalHminusOnePotential) :
    originalCanonicalGapValues (originalHillSpatialTranslation t q)=originalCanonicalGapValues q :=
  originalCanonicalGapValues_isospectral q _ (originalHillSpatialTranslation_isospectral t q)

theorem originalCanonicalHillAction_spatialTranslation (t : ℝ) (q : OriginalHminusOnePotential) (n : ℕ+) :
    originalCanonicalHillAction n (originalHillSpatialTranslation t q)=originalCanonicalHillAction n q := by
  rw [originalCanonicalHillAction_eq_real_gapIntegral,originalCanonicalHillAction_eq_real_gapIntegral,
    originalHillLabels_spatialTranslation,
    originalHillDiscriminant_eq_of_isospectral q _ (originalHillSpatialTranslation_isospectral t q)]

/-- At EVERY original real mean-zero L2 source, the actual action gradient
annihilates the SAME physical spatial derivative. This includes closed gaps
and does not assume a momentum trace or Birkhoff translation covariance. -/
theorem originalCanonicalHillAction_spatial_derivative_zero
    (q : OriginalHminusOnePotential) (u : Coeff 2)
    (hu : periodOneL2Inclusion u=originalPeriodOneCoefficients q) (n : ℕ+) :
    (fderiv ℂ (hillHminusCanonicalAction n) (originalPeriodOneCoefficients q))
      (periodOneL2SpatialDerivative u)=0 := by
  let T := fun t : ℝ => WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t
    (originalPeriodOneCoefficients q)
  have hF : HasFDerivAt (hillHminusCanonicalAction n)
      (fderiv ℂ (hillHminusCanonicalAction n) (originalPeriodOneCoefficients q)) (T 0) := by
    simpa only [T,WeightedCoeff.spatialTranslation_zero] using
      (analyticOnNhd_hillHminusCanonicalAction n _
        (real_mem_hillHminusCanonicalActionDomain _ (originalPeriodOneCoefficients_real q))).differentiableAt.hasFDerivAt
  have hγ : HasDerivAt T (periodOneL2SpatialDerivative u) (0:ℝ) := by
    simpa only [T,hu,WeightedCoeff.spatialTranslation_zero] using
      hasDerivAt_periodOneL2Inclusion_spatialTranslation u 0
  have hd := (hF.restrictScalars ℝ).comp_hasDerivAt (0:ℝ) hγ
  change HasDerivAt (fun t => hillHminusCanonicalAction n (T t))
    ((fderiv ℂ (hillHminusCanonicalAction n) (originalPeriodOneCoefficients q))
      (periodOneL2SpatialDerivative u)) 0 at hd
  have hinv (t : ℝ) : hillHminusCanonicalAction n (T t)=originalCanonicalHillAction n q := by
    dsimp only [T]
    rw [← originalHillSpatialTranslation_coefficients]
    exact originalCanonicalHillAction_spatialTranslation t q n
  simp_rw [hinv] at hd
  exact hd.unique (hasDerivAt_const 0 _)

end NLS.Articles.KdVPseudomeasures
