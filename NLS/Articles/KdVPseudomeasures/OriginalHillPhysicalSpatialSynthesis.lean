import NLS.Articles.KdVPseudomeasures.OriginalHillSmoothPhysicalSolutions
import NLS.Fourier.SpatialTranslation
import NLS.Fourier.PeriodOneSynthesisPhysicalReality

/-! Actual H1 physical synthesis is real and mean zero, and its
spatial coefficient rotations are literal physical translations. -/
noncomputable section
open Complex MeasureTheory NLS.KdV NLS.WeightedCoeff NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.KdVPseudomeasures

def hillPhysicalH1Synthesis (q : RealSignedHilbert (signedStepOrder 0 1)) (x : ℝ) : ℂ :=
  periodOneSobolevSynthesis (signedOneRealToScalarDomain q) (x : AddCircle (2 : ℝ))

theorem hillPhysicalH4Synthesis_coefficients (q : RealSignedHilbert (signedStepOrder 0 4)) (k : ℤ) :
    periodOneCoefficient (hillPhysicalH4Synthesis q) k = q.val.val.val k := by
  change periodOneCoefficient (fun x : ℝ => periodOneSobolevSynthesis
    (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q))
      (x : AddCircle (2 : ℝ))) k = _
  rw [periodOneCoefficient_periodOneSobolevSynthesis,
    signedOneRealToScalarDomain_apply, hillIntegerSourceOrderInclusion_apply]

theorem hillPhysicalH1Synthesis_real (q : RealSignedHilbert (signedStepOrder 0 1)) (x : ℝ) :
    conj (hillPhysicalH1Synthesis q x) = hillPhysicalH1Synthesis q x := by
  let b : Coeff 1 := sobolevToL1CLM 2 (by simp) (signedOneRealToScalarDomain q)
  have hb (k : ℤ) : b (-k) = conj (b k) := by
    dsimp only [b]
    rw [sobolevToL1CLM_apply, sobolevToL1CLM_apply,
      signedOneRealToScalarDomain_apply, signedOneRealToScalarDomain_apply]
    exact q.property k
  simpa only [hillPhysicalH1Synthesis, periodOneSobolevSynthesis_apply, b] using!
    periodOneSynthesis_conj_of_reflection b hb x

theorem hillPhysicalH1Synthesis_mean_zero (q : RealSignedHilbert (signedStepOrder 0 1)) :
    (∫ x in (0 : ℝ)..1, hillPhysicalH1Synthesis q x) = 0 := by
  rw [← periodOneCoefficient_zero_eq_integral]
  change periodOneCoefficient (fun x : ℝ => periodOneSobolevSynthesis
    (signedOneRealToScalarDomain q) (x : AddCircle (2 : ℝ))) 0 = 0
  rw [periodOneCoefficient_periodOneSobolevSynthesis, signedOneRealToScalarDomain_apply]
  exact q.val.property

theorem hillPhysicalH1Synthesis_spatialTranslation
    (q : RealSignedHilbert (signedStepOrder 0 1)) (t x : ℝ) :
    hillPhysicalH1Synthesis
      (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) t q) x =
      hillPhysicalH1Synthesis q (x + t) := by
  have he : sobolevToL1CLM 2 (by simp)
      (signedOneRealToScalarDomain (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) t q)) =
      Coeff.spatialTranslation (2 * Real.pi) t
        (sobolevToL1CLM 2 (by simp) (signedOneRealToScalarDomain q)) := by
    ext k
    simp only [sobolevToL1CLM_apply, signedOneRealToScalarDomain_apply,
      fourierRealZeroSpatialTranslation_apply, Coeff.spatialTranslation_apply]
  have h := congrArg (fun a : Coeff 1 => periodOneSynthesis a x) he
  have h' := h.trans (periodOneSynthesis_spatialTranslation t _ x)
  simpa only [hillPhysicalH1Synthesis, periodOneSobolevSynthesis_apply] using! h'

theorem hillPhysicalH4Synthesis_periodic (q : RealSignedHilbert (signedStepOrder 0 4)) :
    Function.Periodic (hillPhysicalH4Synthesis q) 1 :=
  periodOneSobolevSynthesis_periodic
    (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q))

theorem hillPhysicalH4Synthesis_real (q : RealSignedHilbert (signedStepOrder 0 4)) (x : ℝ) :
    conj (hillPhysicalH4Synthesis q x) = hillPhysicalH4Synthesis q x :=
  hillPhysicalH1Synthesis_real (hillIntegerSourceOrderInclusion 1 4 (by decide) q) x

theorem hillPhysicalH4Synthesis_mean_zero (q : RealSignedHilbert (signedStepOrder 0 4)) :
    (∫ x in (0 : ℝ)..1, hillPhysicalH4Synthesis q x) = 0 :=
  hillPhysicalH1Synthesis_mean_zero (hillIntegerSourceOrderInclusion 1 4 (by decide) q)

end NLS.Articles.KdVPseudomeasures
