import NLS.SequenceSpaces.WeightedPairExponent
import NLS.ZakharovShabat.SourceWeightedRealExponent
import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexDerivative

/-! # Native weighted exponent inclusions and the original source

Forgetting weights commutes with increasing exponents, for both the
complex source and rectangular target. The existing real inclusion agrees.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

@[simp] theorem originalWeightedSourceCLM_exponent (w : SpectralWeight) (hpq : p ≤ q)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) :
    originalWeightedSourceCLM w (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a) =
      CoeffPair.exponentInclusion hpq (originalWeightedSourceCLM w a) := by
  apply (WithLp.equiv q _).injective
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change (originalWeightedSourceCLM w (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a)).fst n =
      (Coeff.exponentInclusion hpq (originalWeightedSourceCLM w a).fst) n
    simp
  · change (originalWeightedSourceCLM w (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a)).snd n =
      (Coeff.exponentInclusion hpq (originalWeightedSourceCLM w a).snd) n
    simp

@[simp] theorem weightedBirkhoffTargetInclusion_exponent (w : SpectralWeight) (hpq : p ≤ q)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) :
    weightedBirkhoffTargetInclusion w (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a) =
      ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)) (weightedBirkhoffTargetInclusion w a) := by
  apply Prod.ext <;> ext n <;> simp

theorem weightedBirkhoffTargetInclusion_injective (w : SpectralWeight) :
    Function.Injective (weightedBirkhoffTargetInclusion (p := p) w) :=
  (CoeffPair.toMax p).injective.comp (originalWeightedSourceCLM_injective w)

@[simp] theorem weightedComplexExponent_real (w : SpectralWeight) (hpq : p ≤ q)
    (a : weightedRealSourceSubmodule (p := p) w) :
    WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a.val =
      (weightedRealSourceExponentInclusion w hpq a).val := rfl

end NLS.ZakharovShabat
