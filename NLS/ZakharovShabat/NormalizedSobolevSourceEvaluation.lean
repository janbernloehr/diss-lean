import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.Fourier.SpatialTranslation
import NLS.SequenceSpaces.SobolevEmbedding

/-! # Bounded physical evaluation of normalized Sobolev sources

The spectral weight at frequency `2n` is chosen to be exactly `1+|n|`.
Decoding then maps boundedly into absolutely summable source coefficients,
so physical evaluation is a bounded complex linear map at every finite p.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A spectral weight giving the original one-derivative source weight after doubling. -/
def sourceOneDerivativeWeight : SpectralWeight :=
  SpectralWeight.scaledSobolev (1/2) 1 (by norm_num) zero_le_one

@[simp] theorem sourceOneDerivativeWeight_double (n : ℤ) :
    sourceOneDerivativeWeight (2*n) = Weight.sobolev 1 n := by
  simp [sourceOneDerivativeWeight, SpectralWeight.scaledSobolev_apply, Weight.sobolev_apply,
    abs_mul]

/-- Decode normalized one-derivative scalar coordinates into absolutely summable coefficients. -/
def normalizedSobolevScalarL1 (hp : p ≠ ⊤) : Coeff p →L[ℂ] Coeff 1 :=
  (WeightedCoeff.sobolevToL1CLM p hp).comp
    (WeightedCoeff.weightIsometry (Weight.sobolev 1) p).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem normalizedSobolevScalarL1_apply (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    normalizedSobolevScalarL1 hp a n = a n / (Weight.sobolev 1 n : ℂ) := by
  change WeightedCoeff.sobolevToL1CLM p hp
    ((WeightedCoeff.weightIsometry (Weight.sobolev 1) p).symm a) n = _
  rw [WeightedCoeff.sobolevToL1CLM_apply]
  rfl

/-- Bounded decoding into the absolutely summable source pair, retaining the coefficients. -/
def normalizedSobolevSourceL1 (hp : p ≠ ⊤) : CoeffPair p →L[ℂ] CoeffPair 1 :=
  (CoeffPair.toMax 1).symm.toContinuousLinearMap.comp
    (((normalizedSobolevScalarL1 hp).prodMap (normalizedSobolevScalarL1 hp)).comp
      (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem normalizedSobolevSourceL1_fst (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) :
    (normalizedSobolevSourceL1 hp φ).fst n =
      (normalizedWeightedSource sourceOneDerivativeWeight φ).fst n := by
  change normalizedSobolevScalarL1 hp φ.fst n = _
  rw [normalizedSobolevScalarL1_apply]
  rw [normalizedWeightedSource_fst, sourceOneDerivativeWeight_double]

@[simp] theorem normalizedSobolevSourceL1_snd (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) :
    (normalizedSobolevSourceL1 hp φ).snd n =
      (normalizedWeightedSource sourceOneDerivativeWeight φ).snd n := by
  change normalizedSobolevScalarL1 hp φ.snd n = _
  rw [normalizedSobolevScalarL1_apply]
  rw [normalizedWeightedSource_snd, sourceOneDerivativeWeight_double]

/-- Period-one physical evaluation is bounded on absolutely summable coefficients. -/
def periodOneEvaluationCLM (x : ℝ) : Coeff 1 →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).comp
    (Fourier.continuousSynthesisCLM.comp Coeff.periodDouble.toContinuousLinearMap)

@[simp] theorem periodOneEvaluationCLM_apply (x : ℝ) (a : Coeff 1) :
    periodOneEvaluationCLM x a = Fourier.periodOneSynthesis a x := rfl

/-- Bounded physical evaluation of both components of a normalized Sobolev source. -/
def normalizedSobolevSourceEvaluation (hp : p ≠ ⊤) (x : ℝ) : CoeffPair p →L[ℂ] ℂ × ℂ :=
  ((periodOneEvaluationCLM x).prodMap (periodOneEvaluationCLM x)).comp
    ((CoeffPair.toMax 1).toContinuousLinearMap.comp (normalizedSobolevSourceL1 hp))

@[simp] theorem normalizedSobolevSourceEvaluation_apply (hp : p ≠ ⊤) (x : ℝ) (φ : CoeffPair p) :
    normalizedSobolevSourceEvaluation hp x φ =
      (Fourier.periodOneSynthesis (normalizedSobolevSourceL1 hp φ).fst x,
       Fourier.periodOneSynthesis (normalizedSobolevSourceL1 hp φ).snd x) := rfl

end NLS.ZakharovShabat
