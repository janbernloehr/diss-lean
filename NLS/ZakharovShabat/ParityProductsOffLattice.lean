import NLS.ZakharovShabat.CompleteParitySpectrum
import NLS.ZakharovShabat.ParitySpectralProducts

/-!
# Exact zeros of the completed parity products off the free lattice

Rescaling reduces both parity products to the standard full paired product.
The completed sequences then identify their zeros with the original parity
algebraic multiplicities.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The filled full paired product retains its selected zeros off the free lattice. -/
theorem entireSpectralPairProduct_eq_zero_offLattice (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    entireSpectralPairProduct ξ η z = 0 ↔ ∃ n : ℤ, ξ n = z ∨ η n = z := by
  rw [entireSpectralPairProduct_eq_offLattice hp ξ η hξ hη z hz]
  exact spectralPairProductOffLattice_eq_zero_iff hp ξ η hξ hη z hz

/-- The even product vanishes exactly at the selected even roots off the free lattice. -/
theorem evenSpectralPairProduct_eq_zero_offLattice (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    evenSpectralPairProduct ξ η z = 0 ↔ ∃ n : ℤ, ξ (2*n) = z ∨ η (2*n) = z := by
  have hz' : z/2 ∉ freeLattice := by
    rintro ⟨n,hn⟩
    apply hz
    refine ⟨2*n, ?_⟩
    push_cast
    linear_combination 2*hn
  rw [evenSpectralPairProduct, entireSpectralPairProduct_eq_zero_offLattice hp _ _
    (memℓp_parityRescale hp ξ hξ 0) (memℓp_parityRescale hp η hη 0) _ hz']
  simp [parityRescale]

/-- The odd product vanishes exactly at the selected odd roots off the free lattice. -/
theorem oddSpectralPairProduct_eq_zero_offLattice (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    oddSpectralPairProduct ξ η z = 0 ↔ ∃ n : ℤ, ξ (2*n+1) = z ∨ η (2*n+1) = z := by
  have hz' : (z-(Real.pi : ℂ))/2 ∉ freeLattice := by
    rintro ⟨n,hn⟩
    apply hz
    refine ⟨2*n+1, ?_⟩
    push_cast
    linear_combination 2*hn
  rw [oddSpectralPairProduct, neg_eq_zero, entireSpectralPairProduct_eq_zero_offLattice hp _ _
    (memℓp_parityRescale hp ξ hξ 1) (memℓp_parityRescale hp η hη 1) _ hz']
  simp [parityRescale]

/-- Completed roots in either residue can be written in the literal source indexing. -/
theorem CompletePeriodicParityPairs.affine_root_iff {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    (∃ n : ℤ, ξ (2*n+r) = z ∨ η (2*n+r) = z) ↔
      0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) r z := by
  rw [← h.root_iff r hr z]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨2*n+r, by omega, hn⟩
  · rintro ⟨n,hn,hz⟩
    refine ⟨n/2, ?_⟩
    have he : 2*(n/2)+r = n := by rcases hr with rfl | rfl <;> omega
    rwa [he]

/-- Both actual parity multiplicities are detected by the entire products off the free lattice. -/
theorem CompletePeriodicParityPairs.products_zero_offLattice {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) (hz : z ∉ freeLattice) :
    (evenSpectralPairProduct ξ η z = 0 ↔ 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 0 z) ∧
    (oddSpectralPairProduct ξ η z = 0 ↔ 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 1 z) := by
  constructor
  · rw [evenSpectralPairProduct_eq_zero_offLattice hp ξ η h.left_displacement h.right_displacement z hz]
    simpa only [add_zero] using h.affine_root_iff 0 (Or.inl rfl) z
  · rw [oddSpectralPairProduct_eq_zero_offLattice hp ξ η h.left_displacement h.right_displacement z hz]
    exact h.affine_root_iff 1 (Or.inr rfl) z

end NLS.ZakharovShabat
