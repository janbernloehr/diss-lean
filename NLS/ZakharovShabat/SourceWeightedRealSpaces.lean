import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.SequenceSpaces.WeightedRealCoeff

/-! # Original weighted real source and target spaces

The source keeps its raw Fourier coefficients and conjugate-reflection condition.
Normalized coordinates give a norm-preserving real equivalence and prove
completeness. The target uses the existing real subspace of weighted coefficients.
-/
noncomputable section
namespace NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Decode normalized weighted coordinates in the original real source space at any Banach exponent. -/
def normalizedWeightedRealSourceLp (w : SpectralWeight) (a : realTypeSourceSubmodule p) :
    realTypeSourceSubmodule p :=
  ⟨normalizedWeightedSource w a.val, normalizedWeightedSource_realType w a.val a.property⟩


/-- The source frequency n corresponds to the even period-two spectral frequency 2n. -/
def sourceFrequencyWeight (w : SpectralWeight) : Weight :=
  ⟨fun n => w (2*n), fun n => w.toWeight.positive (2*n)⟩

/-- Positive weighting preserves the exact component-sum source norm. -/
def sourcePairWeightCoordinates (w : SpectralWeight) :
    WeightedCoeffPair (sourceFrequencyWeight w) p ≃ₗᵢ[ℂ] CoeffPair p :=
  (WeightedCoeff.weightIsometry (sourceFrequencyWeight w) p).withLpProdCongr p
    (WeightedCoeff.weightIsometry (sourceFrequencyWeight w) p)

@[simp] theorem sourcePairWeightCoordinates_fst (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (n : ℤ) :
    (sourcePairWeightCoordinates (p := p) w a).fst n = (w (2*n) : ℂ) * a.fst.val n := rfl

@[simp] theorem sourcePairWeightCoordinates_snd (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (n : ℤ) :
    (sourcePairWeightCoordinates (p := p) w a).snd n = (w (2*n) : ℂ) * a.snd.val n := rfl

/-- The actual weighted real source, with its inherited weighted pair norm. -/
def weightedRealSourceSubmodule (w : SpectralWeight) :
    Submodule ℝ (WeightedCoeffPair (sourceFrequencyWeight w) p) :=
  (realTypeSourceSubmodule p).comap
    (((sourcePairWeightCoordinates (p := p) w).toLinearEquiv.restrictScalars ℝ).toLinearMap)

/-- The real subspace has the original conjugate-reflection condition on raw coefficients. -/
theorem mem_weightedRealSourceSubmodule_iff (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) :
    a ∈ weightedRealSourceSubmodule w ↔ ∀ n : ℤ, a.snd.val n = conj (a.fst.val (-n)) := by
  change (∀ n : ℤ, (w (2*n) : ℂ) * a.snd.val n = conj ((w (2*(-n)) : ℂ) * a.fst.val (-n))) ↔ _
  simp only [mul_neg, SpectralWeight.apply_neg, map_mul, Complex.conj_ofReal,
    mul_right_inj' (w.toWeight.complex_ne_zero _)]

/-- Normalized real coordinates for the original weighted source Banach space. -/
def weightedRealSourceEquiv (w : SpectralWeight) :
    weightedRealSourceSubmodule (p := p) w ≃L[ℝ] realTypeSourceSubmodule p := by
  let e : WeightedCoeffPair (sourceFrequencyWeight w) p ≃L[ℝ] CoeffPair p :=
    { toLinearEquiv := (sourcePairWeightCoordinates (p := p) w).toLinearEquiv.restrictScalars ℝ
      continuous_toFun := (sourcePairWeightCoordinates (p := p) w).continuous
      continuous_invFun := (sourcePairWeightCoordinates (p := p) w).symm.continuous }
  exact e.ofSubmodule' (realTypeSourceSubmodule p)

@[simp] theorem weightedRealSourceEquiv_val (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    (weightedRealSourceEquiv w a).val = sourcePairWeightCoordinates (p := p) w a.val := rfl

/-- The real source coordinate equivalence preserves the original weighted norm. -/
theorem norm_weightedRealSourceEquiv (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) : ‖weightedRealSourceEquiv w a‖ = ‖a‖ :=
  (sourcePairWeightCoordinates (p := p) w).norm_map a.val

/-- The original real source relation is closed in the weighted topology. -/
theorem isClosed_weightedRealSourceSubmodule (w : SpectralWeight) :
    IsClosed (weightedRealSourceSubmodule (p := p) w : Set (WeightedCoeffPair (sourceFrequencyWeight w) p)) :=
  isClosed_realTypeSourceSubmodule.preimage (sourcePairWeightCoordinates (p := p) w).continuous

instance (w : SpectralWeight) : CompleteSpace (weightedRealSourceSubmodule (p := p) w) :=
  (isClosed_weightedRealSourceSubmodule w).completeSpace_coe

/-- Include an original weighted real source in the unweighted source without changing coefficients. -/
def originalWeightedRealSource (w : SpectralWeight) (a : weightedRealSourceSubmodule (p := p) w) :
    realTypeSourceSubmodule p := normalizedWeightedRealSourceLp w (weightedRealSourceEquiv w a)

@[simp] theorem originalWeightedRealSource_fst (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) (n : ℤ) :
    (originalWeightedRealSource w a).val.fst n = a.val.fst.val n := by
  change (normalizedWeightedSource w (weightedRealSourceEquiv w a).val).fst n = _
  rw [normalizedWeightedSource_fst, weightedRealSourceEquiv_val, sourcePairWeightCoordinates_fst,
    mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]

@[simp] theorem originalWeightedRealSource_snd (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) (n : ℤ) :
    (originalWeightedRealSource w a).val.snd n = a.val.snd.val n := by
  change (normalizedWeightedSource w (weightedRealSourceEquiv w a).val).snd n = _
  rw [normalizedWeightedSource_snd, weightedRealSourceEquiv_val, sourcePairWeightCoordinates_snd,
    mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]

@[simp] theorem weightedRealCoeff_inverse_raw (w : Weight) (a : RealCoeff p) (n : ℤ) :
    ((WeightedRealCoeff.weightEquiv w p).symm a).val.val n = (a n : ℂ) / (w n : ℂ) := rfl

/-- Inverse real weighting preserves the weighted norm at every Banach exponent. -/
theorem weightedRealCoeff_inverse_norm (w : Weight) (a : RealCoeff p) :
    ‖(WeightedRealCoeff.weightEquiv w p).symm a‖ = ‖a‖ := by
  have he := Coeff.complex_coordinateRealEquiv (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv
    ((WeightedRealCoeff.weightEquiv w p).symm a)
  change RealCoeff.complexCLM p ((WeightedRealCoeff.weightEquiv w p)
    ((WeightedRealCoeff.weightEquiv w p).symm a)) = _ at he
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  calc
    _ = ‖(WeightedCoeff.weightIsometry w p) ((WeightedRealCoeff.weightEquiv w p).symm a).val‖ :=
      ((WeightedCoeff.weightIsometry w p).norm_map _).symm
    _ = ‖RealCoeff.complexCLM p a‖ := congrArg norm he.symm
    _ = ‖a‖ := by
      apply le_antisymm
      · exact lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' (fun n => by simp)
      · exact lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' (fun n => by simp)


/-- Undo real target weights in both components, with the original lp pair topology. -/
def weightedRealTargetDecode (w : Weight) :
    WithLp p (RealCoeff p × RealCoeff p) ≃ₜ WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  (WithLp.homeomorphProd p _ _).trans
    (((WeightedRealCoeff.weightEquiv w p).symm.toHomeomorph.prodCongr
      (WeightedRealCoeff.weightEquiv w p).symm.toHomeomorph).trans
      (WithLp.homeomorphProd p _ _).symm)

@[simp] theorem weightedRealTargetDecode_fst (w : Weight) (a : WithLp p (RealCoeff p × RealCoeff p)) :
    (weightedRealTargetDecode w a).fst = (WeightedRealCoeff.weightEquiv w p).symm a.fst := rfl

@[simp] theorem weightedRealTargetDecode_snd (w : Weight) (a : WithLp p (RealCoeff p × RealCoeff p)) :
    (weightedRealTargetDecode w a).snd = (WeightedRealCoeff.weightEquiv w p).symm a.snd := rfl

end NLS.ZakharovShabat
