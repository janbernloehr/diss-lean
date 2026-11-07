import NLS.Articles.KdVPseudomeasures.SourceWeightedSpectral
import NLS.Fourier.PeriodicWeightedExponentInclusion

/-! The full complex original Wiener distribution in the identical
weighted-infinity and plain-infinity spectral source models. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.Articles.KdVPseudomeasures

def sourceWienerEndpointCoefficients (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) :
    WeightedCoeff (w.negativeSobolev 0) 1 :=
  coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev 0) q

theorem norm_sourceWienerEndpointCoefficients (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) :
    ‖sourceWienerEndpointCoefficients w q‖ = ‖q‖ :=
  (coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev 0)).norm_map q

def sourceWienerInfinity (w : SpectralWeight) :
    PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1 →L[ℂ]
      PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) ⊤ :=
  weightedExponentInclusion _ (w.hasTemperedInverse_negativeSobolev 0) le_top

theorem sourceWienerInfinity_val (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) :
    (sourceWienerInfinity w q).val = q.val :=
  weightedExponentInclusion_val _ (w.hasTemperedInverse_negativeSobolev 0) le_top q

theorem norm_sourceWienerInfinity_le (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) :
    ‖sourceWienerInfinity w q‖ ≤ ‖q‖ :=
  norm_weightedExponentInclusion_le _ (w.hasTemperedInverse_negativeSobolev 0) le_top q

theorem sourceWienerInfinity_coefficients (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) :
    sourceWeightedEndpointCoefficients w 0 (sourceWienerInfinity w q) =
      WeightedCoeff.exponentInclusion _ (show 1 ≤ (⊤:ℝ≥0∞) from le_top)
        (sourceWienerEndpointCoefficients w q) :=
  weightedExponentInclusion_coefficients _ (w.hasTemperedInverse_negativeSobolev 0) le_top q

def sourceWienerPlain (w : SpectralWeight) :
    PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1 →L[ℂ]
      FourierLebesgueSpace (2:ℝ) (-0) ⊤ :=
  (sourceForgetWeight w 0).comp (sourceWienerInfinity w)

theorem sourceWienerPlain_val (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) :
    (sourceWienerPlain w q).val = q.val :=
  (sourceForgetWeight_val w 0 (sourceWienerInfinity w q)).trans (sourceWienerInfinity_val w q)

theorem norm_sourceWienerPlain_le (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) :
    ‖sourceWienerPlain w q‖ ≤ ‖q‖ :=
  (norm_sourceForgetWeight_le w 0 (sourceWienerInfinity w q)).trans (norm_sourceWienerInfinity_le w q)

theorem sourceWienerPlain_coefficients (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) :
    sourceEndpointCoefficients 0 (sourceWienerPlain w q) =
      endpointForgetWeight w 0 (WeightedCoeff.exponentInclusion _
        (show 1 ≤ (⊤:ℝ≥0∞) from le_top) (sourceWienerEndpointCoefficients w q)) := by
  have h := sourceEndpointCoefficients_forgetWeight w 0 (sourceWienerInfinity w q)
  rwa [sourceWienerInfinity_coefficients] at h

end NLS.Articles.KdVPseudomeasures
