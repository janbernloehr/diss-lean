import NLS.ZakharovShabat.ResonantCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The Section 6 resonant matrix and eigenfunction reconstruction

The two-dimensional map is `S_n=(λ-nπ)Id - coordinates ∘ T̂_n Φ ∘ synthesis`.
Its kernel is equivalent to the kernel of the actual weighted differential
pencil. The determinant criterion follows from this explicit reconstruction.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's resonant map in the physical two-mode basis. -/
def weightedResonantMap (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (z - (Real.pi : ℂ) * n) • ContinuousLinearMap.id ℂ _ -
    (resonantCoordinates w.toWeight n).comp ((weightedCorrection hp w φ n z hz h).comp
      ((weightedDomainPotential hp w φ).comp (resonantSynthesis w.toWeight.oneDerivative n)))

/-- Reconstruct a full domain vector from the resonant amplitudes. -/
def weightedReconstruction (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (Fin 2 → ℂ) →L[ℂ] WeightedDomain w.toWeight p :=
  resonantSynthesis w.toWeight.oneDerivative n +
    (weightedQSolution hp w φ n z hz h).comp (resonantSynthesis w.toWeight.oneDerivative n)

/-- Reconstruction leaves the prescribed resonant amplitudes unchanged. -/
@[simp] theorem resonantCoordinates_reconstruction (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (c : Fin 2 → ℂ) :
    resonantCoordinates w.toWeight.oneDerivative n (weightedReconstruction hp w φ n z hz h c) = c := by
  have hq := congrArg (resonantCoordinates w.toWeight.oneDerivative n)
    (weightedQSolution_nonresonant hp w φ n z hz h (resonantSynthesis w.toWeight.oneDerivative n c))
  simp only [resonantCoordinates_complementary] at hq
  change resonantCoordinates w.toWeight.oneDerivative n (resonantSynthesis w.toWeight.oneDerivative n c +
    weightedQSolution hp w φ n z hz h (resonantSynthesis w.toWeight.oneDerivative n c)) = c
  rw [map_add, resonantCoordinates_synthesis, ← hq, add_zero]

/-- The complete differential residual is exactly the synthesized resonant residual. -/
theorem weightedReconstruction_residual (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (c : Fin 2 → ℂ) :
    weightedFreePencil w.toWeight z (weightedReconstruction hp w φ n z hz h c) -
      weightedDomainPotential hp w φ (weightedReconstruction hp w φ n z hz h c) =
        resonantSynthesis w.toWeight n (weightedResonantMap hp w φ n z hz h c) := by
  let u := resonantSynthesis (p := p) w.toWeight.oneDerivative n c
  let b := weightedCorrection hp w φ n z hz h (weightedDomainPotential hp w φ u)
  change weightedFreePencil w.toWeight z (u + weightedQSolution hp w φ n z hz h u) -
    weightedDomainPotential hp w φ (u + weightedQSolution hp w φ n z hz h u) = _
  rw [map_add, weightedQSolution_equation, weightedQSolution_total_potential]
  change weightedFreePencil w.toWeight z u + complementaryProjection w.toWeight n b - b =
    resonantSynthesis w.toWeight n ((z - (Real.pi : ℂ) * n) • c - resonantCoordinates w.toWeight n b)
  rw [map_sub, resonantSynthesis_coordinates]
  change weightedFreePencil w.toWeight z (resonantSynthesis w.toWeight.oneDerivative n c) + _ - _ = _
  rw [pencil_resonantSynthesis]
  have hb := resonant_add_complementary w.toWeight n b
  conv_lhs => rhs; rw [← hb]
  abel

/-- Every domain eigenvector is reconstructed from its two resonant coefficients. -/
theorem weightedReconstruction_of_eigenvector (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (f : WeightedDomain w.toWeight p)
    (hf : weightedFreePencil w.toWeight z f = weightedDomainPotential hp w φ f) :
    weightedReconstruction hp w φ n z hz h (resonantCoordinates w.toWeight.oneDerivative n f) = f := by
  let u := resonantSynthesis (p := p) w.toWeight.oneDerivative n (resonantCoordinates w.toWeight.oneDerivative n f)
  let v := complementaryProjection w.toWeight.oneDerivative n f
  have huv : u + v = f := by
    dsimp [u, v]
    rw [resonantSynthesis_coordinates]
    exact resonant_add_complementary _ _ _
  have hv : v = weightedQSolution hp w φ n z hz h u := by
    apply weightedQSolution_unique
    · exact complementaryProjection_idempotent _ _ _
    · rw [huv]
      change weightedFreePencil w.toWeight z (complementaryProjection w.toWeight.oneDerivative n f) = _
      rw [pencil_complementaryProjection, hf]
  change u + weightedQSolution hp w φ n z hz h u = f
  rw [← hv, huv]

/-- The resonant kernel parametrizes precisely all nonzero weighted domain eigenvectors. -/
theorem weighted_eigenvector_iff_resonant_kernel (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (∃ f : WeightedDomain w.toWeight p, f ≠ 0 ∧ weightedFreePencil w.toWeight z f = weightedDomainPotential hp w φ f) ↔
      ∃ c : Fin 2 → ℂ, c ≠ 0 ∧ weightedResonantMap hp w φ n z hz h c = 0 := by
  constructor
  · rintro ⟨f, hf0, hf⟩
    let c := resonantCoordinates w.toWeight.oneDerivative n f
    have hr : weightedReconstruction hp w φ n z hz h c = f := weightedReconstruction_of_eigenvector hp w φ n z hz h f hf
    refine ⟨c, ?_, ?_⟩
    · intro hc
      apply hf0
      rw [← hr, hc, map_zero]
    · apply resonantSynthesis_injective (p := p) w.toWeight n
      have he := weightedReconstruction_residual hp w φ n z hz h c
      rw [hr, hf, sub_self] at he
      simpa only [map_zero] using he.symm
  · rintro ⟨c, hc, hs⟩
    refine ⟨weightedReconstruction hp w φ n z hz h c, ?_, ?_⟩
    · intro hf
      apply hc
      have he := congrArg (resonantCoordinates w.toWeight.oneDerivative n) hf
      simpa only [resonantCoordinates_reconstruction, map_zero] using he
    · have he := weightedReconstruction_residual hp w φ n z hz h c
      rw [hs, map_zero] at he
      exact sub_eq_zero.mp he

/-- The `2×2` matrix of `S_n` in the ordered physical Fourier basis. -/
def weightedResonantMatrix (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toMatrix' (weightedResonantMap hp w φ n z hz h).toLinearMap

@[simp] theorem weightedResonantMatrix_mulVec (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (c : Fin 2 → ℂ) :
    (weightedResonantMatrix hp w φ n z hz h).mulVec c = weightedResonantMap hp w φ n z hz h c :=
  LinearMap.toMatrix'_mulVec _ _

/-- Matrix entries in the physical basis: the free diagonal minus the corrected potential coefficient. -/
theorem weightedResonantMatrix_entry (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (i j : Fin 2) :
    weightedResonantMatrix hp w φ n z hz h i j = (if i = j then z - (Real.pi : ℂ) * n else 0) -
      resonantCoordinates w.toWeight n (weightedCorrection hp w φ n z hz h
        (weightedDomainPotential hp w φ (resonantSynthesis w.toWeight.oneDerivative n (Pi.single j 1)))) i := by
  change (z - (Real.pi : ℂ) * n) * (Pi.single j (1 : ℂ) : Fin 2 → ℂ) i - _ = _
  by_cases hij : i = j <;> simp [hij]

/-- The weighted-domain determinant criterion, with explicit reconstruction of eigenvectors. -/
theorem weighted_eigenvector_iff_resonant_det_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (∃ f : WeightedDomain w.toWeight p, f ≠ 0 ∧ weightedFreePencil w.toWeight z f = weightedDomainPotential hp w φ f) ↔
      (weightedResonantMatrix hp w φ n z hz h).det = 0 := by
  rw [weighted_eigenvector_iff_resonant_kernel hp w φ n z hz h]
  simpa only [weightedResonantMatrix_mulVec] using (Matrix.exists_mulVec_eq_zero_iff (M := weightedResonantMatrix hp w φ n z hz h))

end NLS.ZakharovShabat
