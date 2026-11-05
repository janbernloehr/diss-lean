import NLS.FunctionalAnalysis.PeriodicContinuousCurveDerivative
import NLS.FunctionalAnalysis.PeriodicIntegrationByParts
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra
import NLS.SequenceSpaces.SignedSobolevRealScale

/-! Bounded reconstruction in the genuine real mean-zero H1 model from
the continuous spatial derivative. The original unit-period Fourier
normalization is retained at every signed frequency. -/
noncomputable section
open Complex NLS.WeightedCoeff
open scoped ContDiff
namespace NLS.Fourier

def periodOneContinuousCoefficients : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] Coeff 2 :=
  (LinearMap.mkContinuous
    { toFun := Coeff.periodHalve
      map_add' := fun a b => by ext n; rfl
      map_smul' := fun c a => by ext n; rfl }
    1 (fun a => by simpa using Coeff.norm_periodHalve_le a)).comp continuousFourierCLM

theorem periodOneContinuousCoefficients_apply
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) (n : ℤ) :
    periodOneContinuousCoefficients
      (NLS.FunctionalAnalysis.periodicContinuousCircle f hf (by simpa using! hp.nat_mul 2)) n =
      periodOneCoefficient f n := by
  change continuousFourierCLM _ (2 * n) = _
  rw [continuousFourierCLM_apply, ← periodTwoCoefficient_circle]
  exact periodTwoCoefficient_periodic_even f hp (hf.intervalIntegrable 0 1) n

def periodOneContinuousRealZero : C(AddCircle (2 : ℝ), ℂ) →L[ℝ]
    fourierRealZeroSubmodule (Weight.signedSobolev 0) 2 :=
  (fourierRealZeroFullProjection (Weight.signedSobolev 0) (Weight.signedSobolev_neg 0)).comp
    ((((weightIsometry (Weight.signedSobolev 0) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      (periodOneContinuousCoefficients.restrictScalars ℝ))

def periodOneContinuousRecovery : C(AddCircle (2 : ℝ), ℂ) →L[ℝ]
    fourierRealZeroSubmodule (Weight.signedSobolev (0 + 1)) 2 :=
  (signedRealSpatialRecovery 0).comp periodOneContinuousRealZero

theorem periodOneContinuousRecovery_deriv
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (0 + 1)) 2)
    (ha : ∀ k, a.val.val.val k = periodOneCoefficient f k) :
    periodOneContinuousRecovery
      (NLS.FunctionalAnalysis.periodicContinuousCircle (deriv f)
        (contDiff_infty_iff_deriv.mp hf).2.continuous
        (by simpa using! (NLS.FunctionalAnalysis.periodic_deriv f 1 hp).nat_mul 2)) = a := by
  let g := NLS.FunctionalAnalysis.periodicContinuousCircle (deriv f)
    (contDiff_infty_iff_deriv.mp hf).2.continuous
    (by simpa using! (NLS.FunctionalAnalysis.periodic_deriv f 1 hp).nat_mul 2)
  have he : (weightIsometry (Weight.signedSobolev 0) 2).symm
      (periodOneContinuousCoefficients g) = (fourierRealZeroSignedSpatialGenerator 0 a).val.val := by
    apply Subtype.ext
    funext k
    change periodOneContinuousCoefficients g k / (Weight.signedSobolev 0 k : ℂ) = _
    rw [periodOneContinuousCoefficients_apply (deriv f) (contDiff_infty_iff_deriv.mp hf).2.continuous
      (NLS.FunctionalAnalysis.periodic_deriv f 1 hp), fourierRealZeroSignedSpatialGenerator_apply,
      ha, periodOneCoefficient_deriv_of_smooth_periodic f hf hp]
    simp only [Weight.signedSobolev, Real.rpow_zero, ofReal_one, div_one]
    push_cast
    ring
  change signedRealSpatialRecovery 0 (fourierRealZeroFullProjection _ _
    ((weightIsometry (Weight.signedSobolev 0) 2).symm (periodOneContinuousCoefficients g))) = a
  rw [he, fourierRealZeroFullProjection_inclusion, signedRealSpatialRecovery_generator]

end NLS.Fourier
