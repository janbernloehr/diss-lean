import NLS.ZakharovShabat.ActualParityProductOrders

/-!
# Choice-independent actual parity products with exact orders

This strengthens the neighborhood existence theorem by specifying the finite
analytic order at every spectral parameter, using the original root spaces.
Joint potential analyticity and discriminant compatibility are separate tasks.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual even-supported potentials have choice-independent entire parity products with exact original orders. -/
theorem exists_uniform_choiceIndependent_actualParityProducts_with_orders (hp : p ≠ ⊤) (hp1 : 1 < p)
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
    fun _ _ _ hk => hk.products_eq hd⟩

end NLS.ZakharovShabat
