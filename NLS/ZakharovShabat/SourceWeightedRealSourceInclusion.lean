import NLS.ZakharovShabat.SourceWeightedInclusion

/-! # Bounded inclusion of the original weighted real source

The real inclusion retains the raw coefficients and the real source relation.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def originalWeightedRealSourceCLM (w : SpectralWeight) :
    weightedRealSourceSubmodule (p := p) w →L[ℝ] realTypeSourceSubmodule p :=
  ((((originalWeightedSourceCLM (p := p) w).restrictScalars ℝ).comp
    (weightedRealSourceSubmodule (p := p) w).subtypeL).codRestrict
      (realTypeSourceSubmodule p) (fun a => (originalWeightedRealSource w a).property))

@[simp] theorem originalWeightedRealSourceCLM_apply (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    originalWeightedRealSourceCLM w a = originalWeightedRealSource w a := rfl

theorem continuous_originalWeightedRealSource (w : SpectralWeight) :
    Continuous (originalWeightedRealSource (p := p) w) :=
  (originalWeightedRealSourceCLM w).continuous

end NLS.ZakharovShabat
