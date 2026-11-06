import NLS.SequenceSpaces.SpatialTranslation

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem continuous_spatialTranslation (w : Weight) (hp : p ≠ ⊤) (c : ℝ) :
    Continuous (fun x : ℝ × WeightedCoeff w p => spatialTranslation w c x.1 x.2) :=
  continuous_phaseFlow w hp (fun k => c*k)

end NLS.WeightedCoeff
