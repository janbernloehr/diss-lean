import NLS.ZakharovShabat.PeriodOneEmbedding
import NLS.ZakharovShabat.UnitWeightedRealization
import NLS.SequenceSpaces.Reflection

/-!
# Isometric source transport for the spectral closing equations

Period doubling followed by unit weighting embeds the original source
pair isometrically in the weighted physical pair. Reflecting only the
first output component puts the signed negative leading coefficient
back at its original source index. Both maps preserve the component-sum
norm exactly.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Unit weighting preserves the original finite-exponent pair norm. -/
def unitWeightedPairEquiv : CoeffPair p ≃ₗᵢ[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight p).symm.withLpProdCongr p
    (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight p).symm

/-- The isometric physical weighted realization of a period-one source. -/
def sourceWeightedPeriodOne : CoeffPair p →ₗᵢ[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p :=
  unitWeightedPairEquiv.toLinearIsometry.comp periodOnePair

@[simp] theorem sourceWeightedPeriodOne_fst (φ : CoeffPair p) (k : ℤ) :
    (sourceWeightedPeriodOne φ).fst.val k = Coeff.periodDouble φ.fst k := by
  change Coeff.periodDouble φ.fst k/(SpectralWeight.one k : ℂ) = _
  simp

@[simp] theorem sourceWeightedPeriodOne_snd (φ : CoeffPair p) (k : ℤ) :
    (sourceWeightedPeriodOne φ).snd.val k = Coeff.periodDouble φ.snd k := by
  change Coeff.periodDouble φ.snd k/(SpectralWeight.one k : ℂ) = _
  simp

@[simp] theorem sourceWeightedPeriodOne_fst_even (φ : CoeffPair p) (k : ℤ) :
    (sourceWeightedPeriodOne φ).fst.val (2*k) = φ.fst k := by simp

@[simp] theorem sourceWeightedPeriodOne_snd_even (φ : CoeffPair p) (k : ℤ) :
    (sourceWeightedPeriodOne φ).snd.val (2*k) = φ.snd k := by simp

@[simp] theorem norm_sourceWeightedPeriodOne (φ : CoeffPair p) : ‖sourceWeightedPeriodOne φ‖ = ‖φ‖ :=
  sourceWeightedPeriodOne.norm_map φ

/-- The original periodic operator receives exactly the period-one
potential, with the actual source coefficients preserved. -/
theorem weightedBaseToPair_sourceWeightedPeriodOne (φ : CoeffPair p) :
    weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne φ) = periodOnePotential φ := by
  rw [← unitBaseEquiv_eq]
  apply Prod.ext <;> ext k <;> simp [periodOnePotential_apply]

/-- Reverse only the negative component's resonance index. -/
def sourceClosingReflection : CoeffPair p ≃ₗᵢ[ℂ] CoeffPair p :=
  Coeff.reflection.withLpProdCongr p (LinearIsometryEquiv.refl ℂ (Coeff p))

@[simp] theorem sourceClosingReflection_fst (u : CoeffPair p) (n : ℤ) :
    (sourceClosingReflection u).fst n = u.fst (-n) := rfl

@[simp] theorem sourceClosingReflection_snd (u : CoeffPair p) (n : ℤ) :
    (sourceClosingReflection u).snd n = u.snd n := rfl

/-- Transporting an operator from the weighted physical source to the
original source does not increase its full operator norm. -/
theorem norm_sourceClosingTransport_le
    (B : WeightedCoeffPair SpectralWeight.one.toWeight p →L[ℂ] CoeffPair p) :
    ‖sourceClosingReflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (B.comp sourceWeightedPeriodOne.toContinuousLinearMap)‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro x
  change ‖sourceClosingReflection (B (sourceWeightedPeriodOne x))‖ ≤ ‖B‖*‖x‖
  rw [sourceClosingReflection.norm_map]
  simpa only [norm_sourceWeightedPeriodOne] using B.le_opNorm (sourceWeightedPeriodOne x)

end NLS.ZakharovShabat
