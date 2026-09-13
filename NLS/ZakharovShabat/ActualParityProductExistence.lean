import NLS.ZakharovShabat.ActualParityProductZeros

/-!
# Entire parity products for actual potentials

A common open convex neighborhood and central threshold provide completed
actual root sequences for every even-supported potential and larger cutoff.
Their correctly normalized parity products are entire, with locally uniform
cutoff and derivative convergence and precisely the original parity zeros.
These are fixed-potential statements; label independence, joint potential
analyticity, and discriminant compatibility are separate steps.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual finite-potential data supply entire parity products with exact zeros and locally uniform derivatives. -/
theorem exists_uniform_actualParityProducts (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        weightedBaseToPair w ψ ∈ pairParitySubspace 0 →
        ∀ N : ℕ, N₀ ≤ N → ∃ ξ η : ℤ → ℂ,
          CompletePeriodicParityPairs hp w ψ N ξ η ∧
          AnalyticOnNhd ℂ (evenSpectralPairProduct ξ η) Set.univ ∧
          AnalyticOnNhd ℂ (oddSpectralPairProduct ξ η) Set.univ ∧
          TendstoLocallyUniformlyOn (fun M z => evenSpectralPairCutoff ξ η z M)
            (evenSpectralPairProduct ξ η) atTop Set.univ ∧
          TendstoLocallyUniformlyOn (fun M z => oddSpectralPairCutoff ξ η z M)
            (oddSpectralPairProduct ξ η) atTop Set.univ ∧
          TendstoLocallyUniformlyOn (fun M => deriv (fun z => evenSpectralPairCutoff ξ η z M))
            (deriv (evenSpectralPairProduct ξ η)) atTop Set.univ ∧
          TendstoLocallyUniformlyOn (fun M => deriv (fun z => oddSpectralPairCutoff ξ η z M))
            (deriv (oddSpectralPairProduct ξ η)) atTop Set.univ ∧
          ∀ z : ℂ,
            (evenSpectralPairProduct ξ η z = 0 ↔
              0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w ψ) 0 z) ∧
            (oddSpectralPairProduct ξ η z = 0 ↔
              0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w ψ) 1 z) := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ heven N hN
  obtain ⟨ξ,η,hd⟩ := h ψ hψ heven N hN
  have hderiv := tendstoLocallyUniformlyOn_deriv_paritySpectralProducts hp ξ η hd.left_displacement hd.right_displacement
  exact ⟨ξ,η,hd,
    analyticOnNhd_evenSpectralPairProduct hp ξ η hd.left_displacement hd.right_displacement,
    analyticOnNhd_oddSpectralPairProduct hp ξ η hd.left_displacement hd.right_displacement,
    tendstoLocallyUniformlyOn_evenSpectralPairProduct hp ξ η hd.left_displacement hd.right_displacement,
    tendstoLocallyUniformlyOn_oddSpectralPairProduct hp ξ η hd.left_displacement hd.right_displacement,
    hderiv.1, hderiv.2, fun z => ⟨hd.evenProduct_eq_zero_iff z, hd.oddProduct_eq_zero_iff z⟩⟩

end NLS.ZakharovShabat
