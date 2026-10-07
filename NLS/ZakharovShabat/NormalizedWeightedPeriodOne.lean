import NLS.ZakharovShabat.SourceWeightedPeriodOne

/-! # Normalized coordinates for weighted period-one sources

An ordinary sequence represents the weighted Fourier coefficients. Dividing
by the physical weight after period doubling gives an isometric embedding
into the weighted physical space. Thus inverse estimates in these coordinates
control the full weighted norm, rather than only the unweighted source norm.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Remove the weight from normalized coefficients, preserving the weighted norm. -/
def normalizedWeightedPairEquiv (w : SpectralWeight) :
    CoeffPair p ≃ₗᵢ[ℂ] WeightedCoeffPair w.toWeight p :=
  (WeightedCoeff.weightIsometry w.toWeight p).symm.withLpProdCongr p
    (WeightedCoeff.weightIsometry w.toWeight p).symm

/-- Isometric period-one realization of normalized weighted source coordinates. -/
def normalizedWeightedPeriodOne (w : SpectralWeight) :
    CoeffPair p →ₗᵢ[ℂ] WeightedCoeffPair w.toWeight p :=
  (normalizedWeightedPairEquiv w).toLinearIsometry.comp periodOnePair

@[simp] theorem normalizedWeightedPeriodOne_fst (w : SpectralWeight) (φ : CoeffPair p) (k : ℤ) :
    (normalizedWeightedPeriodOne w φ).fst.val k = Coeff.periodDouble φ.fst k / (w k : ℂ) := rfl

@[simp] theorem normalizedWeightedPeriodOne_snd (w : SpectralWeight) (φ : CoeffPair p) (k : ℤ) :
    (normalizedWeightedPeriodOne w φ).snd.val k = Coeff.periodDouble φ.snd k / (w k : ℂ) := rfl

@[simp] theorem normalizedWeightedPeriodOne_fst_even (w : SpectralWeight) (φ : CoeffPair p) (k : ℤ) :
    (normalizedWeightedPeriodOne w φ).fst.val (2*k) = φ.fst k / (w (2*k) : ℂ) := by simp

@[simp] theorem normalizedWeightedPeriodOne_snd_even (w : SpectralWeight) (φ : CoeffPair p) (k : ℤ) :
    (normalizedWeightedPeriodOne w φ).snd.val (2*k) = φ.snd k / (w (2*k) : ℂ) := by simp

@[simp] theorem norm_normalizedWeightedPeriodOne (w : SpectralWeight) (φ : CoeffPair p) :
    ‖normalizedWeightedPeriodOne w φ‖ = ‖φ‖ := (normalizedWeightedPeriodOne w).norm_map φ

/-- The actual normalized source transport contracts operator norms. -/
theorem norm_normalizedWeightedClosingTransport_le (w : SpectralWeight)
    (B : WeightedCoeffPair w.toWeight p →L[ℂ] CoeffPair p) :
    ‖sourceClosingReflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (B.comp (normalizedWeightedPeriodOne w).toContinuousLinearMap)‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro x
  change ‖sourceClosingReflection (B (normalizedWeightedPeriodOne w x))‖ ≤ ‖B‖*‖x‖
  rw [sourceClosingReflection.norm_map]
  simpa only [norm_normalizedWeightedPeriodOne] using B.le_opNorm (normalizedWeightedPeriodOne w x)

end NLS.ZakharovShabat
