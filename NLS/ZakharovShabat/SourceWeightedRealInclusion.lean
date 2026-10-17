import NLS.SequenceSpaces.WeightedRealPairInclusion
import NLS.ZakharovShabat.SourceWeightedInclusion
import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexDerivative
import NLS.ZakharovShabat.SourceWeightedRealMembership

/-! # Reality and coefficient-preserving weighted inclusions

The raw source inclusion reflects the conjugate-reflection condition.
The complex target inclusion commutes with the real target inclusion.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Forgetting a spectral weight preserves and reflects the original real source condition. -/
theorem originalWeightedSourceCLM_mem_real_iff (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) :
    originalWeightedSourceCLM w a ∈ realTypeSourceSubmodule p ↔ a ∈ weightedRealSourceSubmodule w := by
  rw [mem_weightedRealSourceSubmodule_iff]
  change (∀ n : ℤ, (originalWeightedSourceCLM w a).snd n = conj ((originalWeightedSourceCLM w a).fst (-n))) ↔ _
  simp only [originalWeightedSourceCLM_fst,originalWeightedSourceCLM_snd]

/-- Forgetting the weight commutes with complex inclusion of real targets. -/
theorem weightedBirkhoffTargetInclusion_complexCLM (w : SpectralWeight)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p)) :
    weightedBirkhoffTargetInclusion w (WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) z) =
      ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) (originalWeightedRealTarget w z) := by
  apply Prod.ext <;> ext n
  · simp only [weightedBirkhoffTargetInclusion_fst,WeightedCoeffPair.complexCLM_fst]
    exact (originalWeightedRealTarget_fst w z n).symm
  · simp only [weightedBirkhoffTargetInclusion_snd,WeightedCoeffPair.complexCLM_snd]
    exact (originalWeightedRealTarget_snd w z n).symm
end NLS.ZakharovShabat
