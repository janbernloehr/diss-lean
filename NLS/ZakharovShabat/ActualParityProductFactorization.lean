import NLS.ZakharovShabat.ParityProductFactorization
import NLS.ZakharovShabat.ActualParityProductOrderExistence
import NLS.ZakharovShabat.CanonicalPeriodicProduct

/-!
# Actual parity factors of the canonical full product

Completed actual root pairs recover the intrinsic normalized central
polynomials. Their limits therefore identify the product of the two parity
functions with the canonical full product, including its normalization.
The additional discriminant identity `f+2=g-2` remains separate.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The two parity normalizations multiply to the full central normalization. -/
theorem centralParityNormalization_mul (K : ℕ) :
    centralParityNormalization K 0 * centralParityNormalization K 1 = centralSpectralNormalization K :=
  prod_centralParityIndices_mul spectralPairDenominator K

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every sufficiently large literal full cutoff is the intrinsic normalized central polynomial. -/
theorem CompletePeriodicParityPairs.fullCutoff_eq_normalizedCentral {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (K : ℕ) (hK : N ≤ K) (z : ℂ) :
    spectralPairPartialProduct ξ η z K = normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w φ) K z := by
  rw [spectralPairPartialProduct, ← prod_centralParityIndices_mul,
    h.central_factor_prod_eq K hK 0 (Or.inl rfl), h.central_factor_prod_eq K hK 1 (Or.inr rfl),
    div_mul_div_comm, centralParityNormalization_mul, normalizedCentralPeriodicPolynomial,
    centralPeriodicPolynomial_eq_parity_mul hp _ h.even_potential K z]
  ring

/-- Completed actual pairs give exactly the canonical full product, without a residual entire factor. -/
theorem CompletePeriodicParityPairs.fullProduct_eq_canonical {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) :
    entireSpectralPairProduct ξ η = canonicalPeriodicProduct hp (weightedBaseToPair w φ) := by
  funext z
  have ht := (tendstoLocallyUniformlyOn_entireSpectralPairProduct hp ξ η
    h.left_displacement h.right_displacement).tendsto_at (Set.mem_univ z)
  have he : ∀ᶠ K : ℕ in atTop, spectralPairPartialProduct ξ η z K =
      normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w φ) K z := by
    filter_upwards [eventually_ge_atTop N] with K hK
    exact h.fullCutoff_eq_normalizedCentral K hK z
  exact ((ht.congr' he).limUnder_eq).symm

/-- The actual entire parity products multiply to the canonically normalized full periodic product. -/
theorem CompletePeriodicParityPairs.parityProducts_mul_eq_canonical {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) :
    evenSpectralPairProduct ξ η z * oddSpectralPairProduct ξ η z =
      canonicalPeriodicProduct hp (weightedBaseToPair w φ) z := by
  rw [paritySpectralPairProducts_mul hp ξ η h.left_displacement h.right_displacement,
    h.fullProduct_eq_canonical]

/-- Differentiating the factorization gives the full product derivative with both parity contributions. -/
theorem CompletePeriodicParityPairs.deriv_canonical_eq_parity {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) :
    deriv (canonicalPeriodicProduct hp (weightedBaseToPair w φ)) z =
      deriv (evenSpectralPairProduct ξ η) z * oddSpectralPairProduct ξ η z +
        evenSpectralPairProduct ξ η z * deriv (oddSpectralPairProduct ξ η) z := by
  have he : canonicalPeriodicProduct hp (weightedBaseToPair w φ) =
      evenSpectralPairProduct ξ η * oddSpectralPairProduct ξ η :=
    funext (fun t => (h.parityProducts_mul_eq_canonical t).symm)
  rw [he]
  exact deriv_mul
    ((analyticOnNhd_evenSpectralPairProduct hp ξ η h.left_displacement h.right_displacement) z
      (Set.mem_univ z)).differentiableAt
    ((analyticOnNhd_oddSpectralPairProduct hp ξ η h.left_displacement h.right_displacement) z
      (Set.mem_univ z)).differentiableAt

/-- Actual even-supported potentials have choice-independent entire parity factors of the canonical full product. -/
theorem exists_uniform_actualParityFactorization (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        weightedBaseToPair w ψ ∈ pairParitySubspace 0 → ∃ f g : ℂ → ℂ,
          AnalyticOnNhd ℂ f Set.univ ∧ AnalyticOnNhd ℂ g Set.univ ∧
          (∀ z : ℂ,
            (f z = 0 ↔ 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w ψ) 0 z) ∧
            (g z = 0 ↔ 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w ψ) 1 z)) ∧
          (∀ z : ℂ,
            analyticOrderAt f z = (parityAlgebraicMultiplicity hp (weightedBaseToPair w ψ) 0 z : ℕ∞) ∧
            analyticOrderAt g z = (parityAlgebraicMultiplicity hp (weightedBaseToPair w ψ) 1 z : ℕ∞)) ∧
          (∀ z : ℂ, f z * g z = canonicalPeriodicProduct hp (weightedBaseToPair w ψ) z) ∧
          ∀ N : ℕ, ∀ ξ η : ℤ → ℂ, CompletePeriodicParityPairs hp w ψ N ξ η →
            evenSpectralPairProduct ξ η = f ∧ oddSpectralPairProduct ξ η = g := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ heven
  obtain ⟨ξ,η,hd⟩ := h ψ hψ heven N₀ le_rfl
  exact ⟨evenSpectralPairProduct ξ η, oddSpectralPairProduct ξ η,
    analyticOnNhd_evenSpectralPairProduct hp ξ η hd.left_displacement hd.right_displacement,
    analyticOnNhd_oddSpectralPairProduct hp ξ η hd.left_displacement hd.right_displacement,
    fun z => ⟨hd.evenProduct_eq_zero_iff z, hd.oddProduct_eq_zero_iff z⟩,
    fun z => ⟨hd.evenProduct_order z, hd.oddProduct_order z⟩,
    fun z => hd.parityProducts_mul_eq_canonical z,
    fun _ _ _ hk => hk.products_eq hd⟩

end NLS.ZakharovShabat
