import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.ZakharovShabat.SourceRealTypeDecomposition

/-! # Weighted decoding commutes with the physical real-type projection -/
noncomputable section
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem normalizedWeightedSource_sourceConjugation (w : SpectralWeight) (a : CoeffPair p) :
    normalizedWeightedSource w (sourceConjugation a) =
      sourceConjugation (normalizedWeightedSource w a) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · change (normalizedWeightedSource w (sourceConjugation a)).fst =
      (sourceConjugation (normalizedWeightedSource w a)).fst
    ext n
    simp only [normalizedWeightedSource_fst,normalizedWeightedSource_snd,
      sourceConjugation_fst,mul_neg,SpectralWeight.apply_neg,
      map_div₀,Complex.conj_ofReal]
  · change (normalizedWeightedSource w (sourceConjugation a)).snd =
      (sourceConjugation (normalizedWeightedSource w a)).snd
    ext n
    simp only [normalizedWeightedSource_fst,normalizedWeightedSource_snd,
      sourceConjugation_snd,mul_neg,SpectralWeight.apply_neg,
      map_div₀,Complex.conj_ofReal]

/-- Projection before or after decoding gives the same original potential. -/
theorem normalizedWeightedSource_sourceRealPart (w : SpectralWeight) (a : CoeffPair p) :
    normalizedWeightedSource w (sourceRealPart a) =
      sourceRealPart (normalizedWeightedSource w a) := by
  change normalizedWeightedSourceCLM w ((1/2:ℂ) • (a+sourceConjugation a)) = _
  rw [map_smul,map_add]
  simp only [normalizedWeightedSourceCLM_apply,normalizedWeightedSource_sourceConjugation,
    sourceRealPart]

end NLS.ZakharovShabat
