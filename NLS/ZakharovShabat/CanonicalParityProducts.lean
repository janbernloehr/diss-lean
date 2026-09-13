import NLS.ZakharovShabat.CentralParityPolynomialsUniform
import NLS.ZakharovShabat.ActualParityProductFactorization

/-!
# Intrinsic parity products

Normalized central parity polynomials define products from the potential alone.
For actual even-supported potentials these limits equal every admissible
completed-root construction, with the original parity zeros and multiplicities.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The intrinsic parity product, defined without any choice of eigenvalue labels. -/
def canonicalParityProduct (hp : p ≠ ⊤) (φ : PairSpace p) (r : ℤ) (z : ℂ) : ℂ :=
  limUnder atTop (fun M : ℕ => normalizedCentralParityPolynomial hp φ (2*M) r z)

/-- Every admissible actual root construction equals the intrinsic parity limits. -/
theorem CompletePeriodicParityPairs.canonicalParity_eq_products {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (hp1 : 1 < p) :
    canonicalParityProduct hp (weightedBaseToPair w φ) 0 = evenSpectralPairProduct ξ η ∧
    canonicalParityProduct hp (weightedBaseToPair w φ) 1 = oddSpectralPairProduct ξ η := by
  let A := ‖(⟨_,h.left_displacement⟩ : Coeff p)‖
  let B := ‖(⟨_,h.right_displacement⟩ : Coeff p)‖
  have hbound : 0 ≤ max A B := (norm_nonneg _).trans (le_max_left A B)
  have ht (z : ℂ) := tendstoUniformlyOn_normalizedCentralParity_family (X := Unit) hp hp1 w
    (fun _ => φ) N (fun _ => ξ) (fun _ => η) (fun _ => h) (max A B) hbound
    (fun _ => le_max_left A B) (fun _ => le_max_right A B) {z} (isCompact_singleton)
  constructor
  · funext z
    exact ((ht z).1.tendsto_at (show (z,()) ∈ ({z} : Set ℂ) ×ˢ Set.univ from
      ⟨Set.mem_singleton z,Set.mem_univ _⟩)).limUnder_eq
  · funext z
    exact ((ht z).2.tendsto_at (show (z,()) ∈ ({z} : Set ℂ) ×ˢ Set.univ from
      ⟨Set.mem_singleton z,Set.mem_univ _⟩)).limUnder_eq

private theorem exists_completeParityPairs_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      CompletePeriodicParityPairs hp SpectralWeight.one (unitBaseEquiv.symm φ) N ξ η := by
  obtain ⟨N,_,U,_,_,hU,_,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 SpectralWeight.one
    (unitBaseEquiv.symm φ)
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨N,h _ hU (by rw [he]; exact hφ) N le_rfl⟩

/-- Intrinsic parity products are entire and have exactly the original parity orders and zeros. -/
theorem canonicalParityProduct_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (hr : r = 0 ∨ r = 1) :
    AnalyticOnNhd ℂ (canonicalParityProduct hp φ r) Set.univ ∧ ∀ z : ℂ,
      analyticOrderAt (canonicalParityProduct hp φ r) z = (parityAlgebraicMultiplicity hp φ r z : ℕ∞) ∧
      (canonicalParityProduct hp φ r z = 0 ↔ 0 < parityAlgebraicMultiplicity hp φ r z) := by
  obtain ⟨N,ξ,η,h⟩ := exists_completeParityPairs_one hp hp1 φ hφ
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  have hcan := h.canonicalParity_eq_products hp1
  rw [he] at hcan
  rcases hr with rfl | rfl
  · rw [hcan.1]
    exact ⟨analyticOnNhd_evenSpectralPairProduct hp ξ η h.left_displacement h.right_displacement,
      fun z => ⟨by simpa only [he] using h.evenProduct_order z,
        by simpa only [he] using h.evenProduct_eq_zero_iff z⟩⟩
  · rw [hcan.2]
    exact ⟨analyticOnNhd_oddSpectralPairProduct hp ξ η h.left_displacement h.right_displacement,
      fun z => ⟨by simpa only [he] using h.oddProduct_order z,
        by simpa only [he] using h.oddProduct_eq_zero_iff z⟩⟩

/-- The two intrinsic parity products factor the canonically normalized full product. -/
theorem canonicalParityProducts_mul (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalParityProduct hp φ 0 z * canonicalParityProduct hp φ 1 z = canonicalPeriodicProduct hp φ z := by
  obtain ⟨N,ξ,η,h⟩ := exists_completeParityPairs_one hp hp1 φ hφ
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  have hcan := h.canonicalParity_eq_products hp1
  rw [he] at hcan
  rw [hcan.1,hcan.2]
  simpa only [he] using h.parityProducts_mul_eq_canonical z

end NLS.ZakharovShabat
