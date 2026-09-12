import NLS.SequenceSpaces.ShiftedWeight
import NLS.Fourier.WeightedDistributionSynthesis
import NLS.Fourier.DistributionModulation

/-!
# Shifted spectral weights and actual physical modulation

For every Section 6 weight, the weighted coefficients define a genuine
periodic tempered distribution. The coefficient modulation used in the
shifted norm is exactly multiplication by the physical Fourier wave.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Spectral-weight synthesis agrees with the contractive unweighted realization. -/
theorem spectralWeight_synthesis_eq (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) :
    weightedDistributionSynthesis w.toWeight w.hasTemperedInverse a = distributionSynthesis (w.toCoeff a) :=
  weightedDistributionSynthesis_eq_distributionSynthesis _ _ _ _ (fun n => (w.toCoeff_apply a n).symm)

/-- Section 6's shifted norm uses genuine multiplication by the physical wave `exp(iπkx)`. -/
theorem spectralWeight_synthesis_modulation (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    weightedDistributionSynthesis w.toWeight w.hasTemperedInverse (w.modulation i a) =
      TemperedDistribution.smulLeftCLM ℂ (wave i) (weightedDistributionSynthesis w.toWeight w.hasTemperedInverse a) := by
  rw [spectralWeight_synthesis_eq, w.toCoeff_modulation, distributionSynthesis_shift, spectralWeight_synthesis_eq]

end NLS.Fourier
