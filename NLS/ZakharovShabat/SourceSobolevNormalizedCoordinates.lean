import NLS.ZakharovShabat.SourceSobolevEmbedding
import NLS.ZakharovShabat.NormalizedWeightedSource

/-! # H¹ coordinates for the weighted closing inverse

The original coefficient at n is multiplied by the physical weight
1+2|n|. This is continuously equivalent to the H¹ weight 1+|n|.
Both directions preserve the actual physical source after unweighting.
-/
noncomputable section
open Complex
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

private def doubledSobolevWeight : Weight :=
  ⟨fun n => (SpectralWeight.sobolev 1 (by norm_num)) (2*n),
    fun n => (SpectralWeight.sobolev 1 (by norm_num)).positive (2*n)⟩

private theorem doubledSobolevWeight_apply (n : ℤ) :
    doubledSobolevWeight n = 1 + 2*|(n : ℝ)| := by
  simp [doubledSobolevWeight, SpectralWeight.sobolev_apply, Weight.sobolev_apply, abs_mul]

private def toDoubledSobolev : ScalarDomain 2 →L[ℂ] WeightedCoeff doubledSobolevWeight 2 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) 2 (by norm_num) (by
    intro n
    simp only [norm_one, mul_one, doubledSobolevWeight_apply, Weight.sobolev_apply, Real.rpow_one]
    linarith)

private def fromDoubledSobolev : WeightedCoeff doubledSobolevWeight 2 →L[ℂ] ScalarDomain 2 :=
  WeightedCoeff.inclusionCLM _ _ (by
    intro n
    simp only [doubledSobolevWeight_apply, Weight.sobolev_apply, Real.rpow_one]
    linarith [abs_nonneg (n : ℝ)])

private def doubledSobolevEquiv : ScalarDomain 2 ≃L[ℂ] WeightedCoeff doubledSobolevWeight 2 :=
  ContinuousLinearEquiv.equivOfInverse toDoubledSobolev fromDoubledSobolev
    (by intro a; apply Subtype.ext; funext n; simp [toDoubledSobolev, fromDoubledSobolev])
    (by intro a; apply Subtype.ext; funext n; simp [toDoubledSobolev, fromDoubledSobolev])

private def scalarSobolevNormalizedCoordinates : ScalarDomain 2 ≃L[ℂ] Coeff 2 :=
  doubledSobolevEquiv.trans (WeightedCoeff.weightIsometry doubledSobolevWeight 2).toContinuousLinearEquiv

/-- Normalized weighted source coordinates, with equivalent H¹ topology. -/
def sobolevNormalizedCoordinates : (ScalarDomain 2 × ScalarDomain 2) ≃L[ℂ] CoeffPair 2 :=
  (scalarSobolevNormalizedCoordinates.prodCongr scalarSobolevNormalizedCoordinates).trans
    (CoeffPair.toMax 2).symm

@[simp] theorem sobolevNormalizedCoordinates_fst (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sobolevNormalizedCoordinates a).fst n =
      ((SpectralWeight.sobolev 1 (by norm_num)) (2*n) : ℂ)*a.1.val n := by
  change (doubledSobolevWeight n : ℂ)*(toDoubledSobolev a.1).val n = _
  change (doubledSobolevWeight n : ℂ)*(1*a.1.val n) = _
  rw [one_mul]
  rfl

@[simp] theorem sobolevNormalizedCoordinates_snd (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sobolevNormalizedCoordinates a).snd n =
      ((SpectralWeight.sobolev 1 (by norm_num)) (2*n) : ℂ)*a.2.val n := by
  change (doubledSobolevWeight n : ℂ)*(toDoubledSobolev a.2).val n = _
  change (doubledSobolevWeight n : ℂ)*(1*a.2.val n) = _
  rw [one_mul]
  rfl

/-- Decoding normalized coordinates recovers the unchanged original H¹ source. -/
theorem normalizedWeightedSource_sobolevNormalizedCoordinates (a : ScalarDomain 2 × ScalarDomain 2) :
    normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) (sobolevNormalizedCoordinates a) =
      sobolevSourceInclusion a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (normalizedWeightedSource _ (sobolevNormalizedCoordinates a)).fst n = (sobolevSourceInclusion a).fst n
    rw [normalizedWeightedSource_fst, sobolevNormalizedCoordinates_fst, sobolevSourceInclusion_fst]
    exact mul_div_cancel_left₀ _ ((SpectralWeight.sobolev 1 (by norm_num)).toWeight.complex_ne_zero _)
  · change (normalizedWeightedSource _ (sobolevNormalizedCoordinates a)).snd n = (sobolevSourceInclusion a).snd n
    rw [normalizedWeightedSource_snd, sobolevNormalizedCoordinates_snd, sobolevSourceInclusion_snd]
    exact mul_div_cancel_left₀ _ ((SpectralWeight.sobolev 1 (by norm_num)).toWeight.complex_ne_zero _)

/-- The normalized weighted physical realization is the original doubled H¹ source. -/
theorem normalizedWeightedPeriodOne_sobolevNormalizedCoordinates (a : ScalarDomain 2 × ScalarDomain 2) :
    normalizedWeightedPeriodOne (SpectralWeight.sobolev 1 (by norm_num)) (sobolevNormalizedCoordinates a) =
      sobolevSourceWeightedPeriodOne a := by
  apply (WeightedCoeffPair.toMax _ 2).injective
  apply Prod.ext
  · apply Subtype.ext
    funext n
    change (normalizedWeightedPeriodOne _ (sobolevNormalizedCoordinates a)).fst.val n =
      (sobolevSourceWeightedPeriodOne a).fst.val n
    by_cases hn : n % 2 = 0
    · have he : n = 2*(n/2) := by omega
      rw [he, normalizedWeightedPeriodOne_fst_even, sobolevNormalizedCoordinates_fst,
        sobolevSourceWeightedPeriodOne_fst, Coeff.periodDouble_even, scalarInclusion_apply]
      exact mul_div_cancel_left₀ _ ((SpectralWeight.sobolev 1 (by norm_num)).toWeight.complex_ne_zero _)
    · have he : n = 2*(n/2)+1 := by omega
      rw [he]
      simp
  · apply Subtype.ext
    funext n
    change (normalizedWeightedPeriodOne _ (sobolevNormalizedCoordinates a)).snd.val n =
      (sobolevSourceWeightedPeriodOne a).snd.val n
    by_cases hn : n % 2 = 0
    · have he : n = 2*(n/2) := by omega
      rw [he, normalizedWeightedPeriodOne_snd_even, sobolevNormalizedCoordinates_snd,
        sobolevSourceWeightedPeriodOne_snd, Coeff.periodDouble_even, scalarInclusion_apply]
      exact mul_div_cancel_left₀ _ ((SpectralWeight.sobolev 1 (by norm_num)).toWeight.complex_ne_zero _)
    · have he : n = 2*(n/2)+1 := by omega
      rw [he]
      simp

/-- The coordinate equivalence preserves the real-type condition in both directions. -/
theorem sobolevNormalizedCoordinates_realType_iff (a : ScalarDomain 2 × ScalarDomain 2) :
    IsRealType (CoeffPair.toMax 2 (sobolevNormalizedCoordinates a)) ↔
      IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)) := by
  constructor
  · intro h
    simpa only [normalizedWeightedSource_sobolevNormalizedCoordinates] using
      normalizedWeightedSource_realType (SpectralWeight.sobolev 1 (by norm_num)) (sobolevNormalizedCoordinates a) h
  · intro h n
    change (sobolevNormalizedCoordinates a).snd n = conj ((sobolevNormalizedCoordinates a).fst (-n))
    simp only [sobolevNormalizedCoordinates_snd, sobolevNormalizedCoordinates_fst,
      mul_neg, SpectralWeight.apply_neg, map_mul, Complex.conj_ofReal]
    have hn := h n
    change (sobolevSourceInclusion a).snd n = conj ((sobolevSourceInclusion a).fst (-n)) at hn
    rw [sobolevSourceInclusion_snd, sobolevSourceInclusion_fst] at hn
    exact congrArg (fun z : ℂ => ((SpectralWeight.sobolev 1 (by norm_num)) (2*n) : ℂ)*z) hn

end NLS.ZakharovShabat
