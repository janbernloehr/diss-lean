import NLS.ZakharovShabat.SourceSobolevEmbedding
import NLS.ZakharovShabat.NormalizedWeightedSourceTopology

/-! # Original source spaces at every integer Sobolev order

The source uses the standard weight (1+|n|)^s. Normalized coordinates use
(1+2|n|)^s; an explicit factor 2^s proves equivalent topologies. Decoding
recovers exactly the original Fourier coefficients.
-/
noncomputable section
open Complex
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- The original pair of period-one Hˢ Fourier coefficient spaces. -/
abbrev SobolevSource (s : ℕ) :=
  WeightedCoeff (Weight.sobolev (s : ℝ)) 2 × WeightedCoeff (Weight.sobolev (s : ℝ)) 2

variable (s : ℕ)

private def higherDoubledSobolevWeight : Weight :=
  ⟨fun n => (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (2*n),
    fun n => (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)).positive (2*n)⟩

private theorem higherDoubledSobolevWeight_apply (n : ℤ) :
    (higherDoubledSobolevWeight s) n = (1 + 2*|(n : ℝ)|)^s := by
  simp [higherDoubledSobolevWeight, SpectralWeight.sobolev_apply, Weight.sobolev_apply, abs_mul, Real.rpow_natCast]

private def toHigherDoubledSobolev : WeightedCoeff (Weight.sobolev (s : ℝ)) 2 →L[ℂ] WeightedCoeff (higherDoubledSobolevWeight s) 2 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) ((2:ℝ)^s) (by positivity) (by
    intro n
    simp only [norm_one, mul_one, higherDoubledSobolevWeight_apply, Weight.sobolev_apply, Real.rpow_natCast]
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    linarith)

private def fromHigherDoubledSobolev : WeightedCoeff (higherDoubledSobolevWeight s) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (s : ℝ)) 2 :=
  WeightedCoeff.inclusionCLM _ _ (by
    intro n
    simp only [higherDoubledSobolevWeight_apply, Weight.sobolev_apply, Real.rpow_natCast]
    apply pow_le_pow_left₀ (by positivity)
    linarith [abs_nonneg (n : ℝ)])

private def higherDoubledSobolevEquiv : WeightedCoeff (Weight.sobolev (s : ℝ)) 2 ≃L[ℂ] WeightedCoeff (higherDoubledSobolevWeight s) 2 :=
  ContinuousLinearEquiv.equivOfInverse (toHigherDoubledSobolev s) (fromHigherDoubledSobolev s)
    (by intro a; apply Subtype.ext; funext n; simp [toHigherDoubledSobolev, fromHigherDoubledSobolev])
    (by intro a; apply Subtype.ext; funext n; simp [toHigherDoubledSobolev, fromHigherDoubledSobolev])

private def scalarHigherSobolevNormalizedCoordinates : WeightedCoeff (Weight.sobolev (s : ℝ)) 2 ≃L[ℂ] Coeff 2 :=
  (higherDoubledSobolevEquiv s).trans (WeightedCoeff.weightIsometry (higherDoubledSobolevWeight s) 2).toContinuousLinearEquiv

/-- Normalized weighted coordinates with the original Hˢ topology. -/
def higherSobolevNormalizedCoordinates : (SobolevSource s) ≃L[ℂ] CoeffPair 2 :=
  ((scalarHigherSobolevNormalizedCoordinates s).prodCongr (scalarHigherSobolevNormalizedCoordinates s)).trans
    (CoeffPair.toMax 2).symm

@[simp] theorem higherSobolevNormalizedCoordinates_fst (a : SobolevSource s) (n : ℤ) :
    ((higherSobolevNormalizedCoordinates s) a).fst n =
      ((SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (2*n) : ℂ)*a.1.val n := by
  change ((higherDoubledSobolevWeight s) n : ℂ)*((toHigherDoubledSobolev s) a.1).val n = _
  change ((higherDoubledSobolevWeight s) n : ℂ)*(1*a.1.val n) = _
  rw [one_mul]
  rfl

@[simp] theorem higherSobolevNormalizedCoordinates_snd (a : SobolevSource s) (n : ℤ) :
    ((higherSobolevNormalizedCoordinates s) a).snd n =
      ((SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (2*n) : ℂ)*a.2.val n := by
  change ((higherDoubledSobolevWeight s) n : ℂ)*((toHigherDoubledSobolev s) a.2).val n = _
  change ((higherDoubledSobolevWeight s) n : ℂ)*(1*a.2.val n) = _
  rw [one_mul]
  rfl

/-- Forget regularity, preserving all original Fourier coefficients. -/
def higherSobolevSourceInclusion : SobolevSource s →L[ℂ] CoeffPair 2 :=
  (normalizedWeightedSourceCLM (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s))).comp
    (higherSobolevNormalizedCoordinates s).toContinuousLinearMap

@[simp] theorem higherSobolevSourceInclusion_fst (a : SobolevSource s) (n : ℤ) :
    (higherSobolevSourceInclusion s a).fst n = a.1.val n := by
  change (normalizedWeightedSource (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (higherSobolevNormalizedCoordinates s a)).fst n = _
  rw [normalizedWeightedSource_fst, higherSobolevNormalizedCoordinates_fst]
  exact mul_div_cancel_left₀ _ ((SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)).toWeight.complex_ne_zero _)

@[simp] theorem higherSobolevSourceInclusion_snd (a : SobolevSource s) (n : ℤ) :
    (higherSobolevSourceInclusion s a).snd n = a.2.val n := by
  change (normalizedWeightedSource (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (higherSobolevNormalizedCoordinates s a)).snd n = _
  rw [normalizedWeightedSource_snd, higherSobolevNormalizedCoordinates_snd]
  exact mul_div_cancel_left₀ _ ((SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)).toWeight.complex_ne_zero _)

/-- The same physical source at even indices, retaining the full Hˢ weight. -/
def higherSobolevSourceWeightedPeriodOne : SobolevSource s →L[ℂ]
    WeightedCoeffPair (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)).toWeight 2 :=
  (normalizedWeightedPeriodOne (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s))).toContinuousLinearMap.comp
    (higherSobolevNormalizedCoordinates s).toContinuousLinearMap

/-- The weighted realization supplies exactly the original spectral operator. -/
theorem weightedBaseToPair_higherSobolevSourceWeightedPeriodOne (a : SobolevSource s) :
    weightedBaseToPair (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s))
      (higherSobolevSourceWeightedPeriodOne s a) = periodOnePotential (higherSobolevSourceInclusion s a) :=
  weightedBaseToPair_normalizedWeightedPeriodOne _ _

/-- The coordinate equivalence preserves the real-type condition in both directions. -/
theorem higherSobolevNormalizedCoordinates_realType_iff (a : SobolevSource s) :
    IsRealType (CoeffPair.toMax 2 (higherSobolevNormalizedCoordinates s a)) ↔
      IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a)) := by
  constructor
  · intro h
    exact normalizedWeightedSource_realType (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s))
      (higherSobolevNormalizedCoordinates s a) h
  · intro h n
    change (higherSobolevNormalizedCoordinates s a).snd n = conj ((higherSobolevNormalizedCoordinates s a).fst (-n))
    simp only [higherSobolevNormalizedCoordinates_snd, higherSobolevNormalizedCoordinates_fst,
      mul_neg, SpectralWeight.apply_neg, map_mul, Complex.conj_ofReal]
    have hn := h n
    change (higherSobolevSourceInclusion s a).snd n = conj ((higherSobolevSourceInclusion s a).fst (-n)) at hn
    rw [higherSobolevSourceInclusion_snd, higherSobolevSourceInclusion_fst] at hn
    exact congrArg (fun z : ℂ => ((SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (2*n) : ℂ)*z) hn

private def higherSobolevScalarOneEquiv : ScalarDomain 2 ≃L[ℂ]
    WeightedCoeff (Weight.sobolev ((1 : ℕ) : ℝ)) 2 :=
  ContinuousLinearEquiv.equivOfInverse
    (WeightedCoeff.inclusionCLM _ _ (by intro n; simp))
    (WeightedCoeff.inclusionCLM _ _ (by intro n; simp))
    (by intro a; apply Subtype.ext; funext n; simp)
    (by intro a; apply Subtype.ext; funext n; simp)

/-- Coefficient-preserving identification with the existing H¹ pair space. -/
def higherSobolevSourceOneEquiv : (ScalarDomain 2 × ScalarDomain 2) ≃L[ℂ] SobolevSource 1 :=
  higherSobolevScalarOneEquiv.prodCongr higherSobolevScalarOneEquiv

/-- The order-one identification recovers the established physical source. -/
theorem higherSobolevSourceInclusion_one (a : ScalarDomain 2 × ScalarDomain 2) :
    higherSobolevSourceInclusion 1 (higherSobolevSourceOneEquiv a) = sobolevSourceInclusion a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (higherSobolevSourceInclusion 1 (higherSobolevSourceOneEquiv a)).fst n = (sobolevSourceInclusion a).fst n
    rw [higherSobolevSourceInclusion_fst, sobolevSourceInclusion_fst]
    change 1 * a.1.val n = a.1.val n
    exact one_mul _
  · change (higherSobolevSourceInclusion 1 (higherSobolevSourceOneEquiv a)).snd n = (sobolevSourceInclusion a).snd n
    rw [higherSobolevSourceInclusion_snd, sobolevSourceInclusion_snd]
    change 1 * a.2.val n = a.2.val n
    exact one_mul _

end NLS.ZakharovShabat
