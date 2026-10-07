import NLS.ZakharovShabat.NormalizedWeightedSource

/-! # Continuous decoding of normalized weighted sources

The actual coefficient decoder is a continuous complex linear map.
Its injectivity permits identification of weighted lifts in the original
source space without changing the Fourier coefficients.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def periodHalveCLM : Coeff p →L[ℂ] Coeff p :=
  LinearMap.mkContinuous
    { toFun := Coeff.periodHalve
      map_add' := by intro a b; ext n; rfl
      map_smul' := by intro c a; ext n; rfl }
    1 (by
      intro a
      change ‖Coeff.periodHalve a‖ ≤ 1*‖a‖
      simpa only [one_mul] using Coeff.norm_periodHalve_le a)

/-- The actual normalized weighted source decoder as a bounded linear map. -/
def normalizedWeightedSourceCLM (w : SpectralWeight) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((periodHalveCLM.prodMap periodHalveCLM).comp
      ((weightedBaseToPair w).comp (normalizedWeightedPeriodOne w).toContinuousLinearMap))

@[simp] theorem normalizedWeightedSourceCLM_apply (w : SpectralWeight) (φ : CoeffPair p) :
    normalizedWeightedSourceCLM w φ = normalizedWeightedSource w φ := rfl

/-- Decoding weighted coefficients is continuous in the original source norm. -/
theorem continuous_normalizedWeightedSource (w : SpectralWeight) :
    Continuous (normalizedWeightedSource (p := p) w) :=
  (normalizedWeightedSourceCLM w).continuous

/-- The actual source determines its normalized weighted coordinates uniquely. -/
theorem normalizedWeightedSource_injective (w : SpectralWeight) :
    Function.Injective (normalizedWeightedSource (p := p) w) := by
  intro φ ψ h
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · have he := congrArg (fun a : CoeffPair p => a.fst n) h
    simp only [normalizedWeightedSource_fst] at he
    exact (div_left_inj' (w.toWeight.complex_ne_zero _)).mp he
  · have he := congrArg (fun a : CoeffPair p => a.snd n) h
    simp only [normalizedWeightedSource_snd] at he
    exact (div_left_inj' (w.toWeight.complex_ne_zero _)).mp he

end NLS.ZakharovShabat
