import NLS.ZakharovShabat.SourceWeightedRealSpaces
import NLS.SequenceSpaces.WeightedSingle
import NLS.SequenceSpaces.SobolevPairCotangent

/-! # The original complex weighted source inclusion

The bounded complex linear inclusion preserves both raw Fourier sequences,
agrees with the original real inclusion, and preserves finite Fourier directions.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Include the native complex weighted source without changing its raw Fourier coefficients. -/
def originalWeightedSourceCLM (w : SpectralWeight) :
    WeightedCoeffPair (sourceFrequencyWeight w) p →L[ℂ] CoeffPair p :=
  (normalizedWeightedSourceCLM w).comp
    (sourcePairWeightCoordinates w).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem originalWeightedSourceCLM_fst (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (n : ℤ) :
    (originalWeightedSourceCLM w a).fst n = a.fst.val n := by
  change (normalizedWeightedSource w (sourcePairWeightCoordinates w a)).fst n = _
  rw [normalizedWeightedSource_fst,sourcePairWeightCoordinates_fst,
    mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]

@[simp] theorem originalWeightedSourceCLM_snd (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (n : ℤ) :
    (originalWeightedSourceCLM w a).snd n = a.snd.val n := by
  change (normalizedWeightedSource w (sourcePairWeightCoordinates w a)).snd n = _
  rw [normalizedWeightedSource_snd,sourcePairWeightCoordinates_snd,
    mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]

@[simp] theorem originalWeightedSourceCLM_real (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    originalWeightedSourceCLM w a.val = (originalWeightedRealSource w a).val := rfl

@[simp] theorem originalWeightedSourceCLM_inl_single (w : SpectralWeight) (n : ℤ) (c : ℂ) :
    originalWeightedSourceCLM (p := p) w
      (WeightedCoeffPair.inlCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ n c)) =
        CoeffPair.inlCLM (lp.single p n c) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext j <;> simp

@[simp] theorem originalWeightedSourceCLM_inr_single (w : SpectralWeight) (n : ℤ) (c : ℂ) :
    originalWeightedSourceCLM (p := p) w
      (WeightedCoeffPair.inrCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ n c)) =
        CoeffPair.inrCLM (lp.single p n c) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext j <;> simp

/-- The original source still determines its native weighted representative uniquely. -/
theorem originalWeightedSourceCLM_injective (w : SpectralWeight) :
    Function.Injective (originalWeightedSourceCLM (p := p) w) := by
  intro a b h
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · change a.fst.val n = b.fst.val n
    simpa only [originalWeightedSourceCLM_fst] using congrArg (fun z : CoeffPair p => z.fst n) h
  · change a.snd.val n = b.snd.val n
    simpa only [originalWeightedSourceCLM_snd] using congrArg (fun z : CoeffPair p => z.snd n) h

end NLS.ZakharovShabat
