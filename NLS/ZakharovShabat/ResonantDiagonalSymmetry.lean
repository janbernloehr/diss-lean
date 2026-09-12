import NLS.ZakharovShabat.BilinearGreen
import NLS.ZakharovShabat.WeightedResonantReduction

/-!
# Lemma 6.7(i): equality of the resonant diagonal coefficients

The bilinear Green identity descends to the two resonant coordinates through
the exact reconstruction residual. It forces equality of the two diagonal
entries for arbitrary complex potentials and every finite Banach exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Testing a resonant vector reads the opposite resonant component of the domain vector. -/
theorem weightedGreenPairing_synthesis (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (c : Fin 2 → ℂ) (f : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w (resonantSynthesis w.toWeight n c) f =
      c 0 * resonantCoordinates w.toWeight.oneDerivative n f 1 +
        c 1 * resonantCoordinates w.toWeight.oneDerivative n f 0 := by
  simp [weightedGreenPairing_apply, ite_mul]

/-- Green's identity on the reconstructed vectors becomes the symmetric cross-coordinate identity. -/
theorem weightedResonantMap_bilinear_symm (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (c d : Fin 2 → ℂ) :
    weightedResonantMap hp w φ n z hz h c 0 * d 1 + weightedResonantMap hp w φ n z hz h c 1 * d 0 =
      weightedResonantMap hp w φ n z hz h d 0 * c 1 + weightedResonantMap hp w φ n z hz h d 1 * c 0 := by
  have hg := weightedGreenPairing_residual_symm hp w φ z
    (weightedReconstruction hp w φ n z hz h c) (weightedReconstruction hp w φ n z hz h d)
  rw [weightedReconstruction_residual, weightedReconstruction_residual] at hg
  simpa only [weightedGreenPairing_synthesis, resonantCoordinates_reconstruction] using hg

/-- The two diagonal entries of the actual reduced differential matrix agree. -/
theorem weightedResonantMatrix_diagonal_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantMatrix hp w φ n z hz h 0 0 = weightedResonantMatrix hp w φ n z hz h 1 1 := by
  change weightedResonantMap hp w φ n z hz h (Pi.single 0 1) 0 = weightedResonantMap hp w φ n z hz h (Pi.single 1 1) 1
  simpa using weightedResonantMap_bilinear_symm hp w φ n z hz h (Pi.single 0 1) (Pi.single 1 1)

/-- The source's correction matrix `P_n T̂_n Φ`, in the ordered physical resonant basis. -/
def weightedCorrectionMatrix (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  resonantCoordinates w.toWeight n (weightedCorrection hp w φ n z hz h
    (weightedDomainPotential hp w φ (resonantSynthesis w.toWeight.oneDerivative n (Pi.single j 1)))) i

/-- Lemma 6.7(i): the source's two potential-correction diagonals are equal. -/
theorem weightedCorrectionMatrix_diagonal_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedCorrectionMatrix hp w φ n z hz h 0 0 = weightedCorrectionMatrix hp w φ n z hz h 1 1 := by
  have he := weightedResonantMatrix_diagonal_eq hp w φ n z hz h
  simp only [weightedResonantMatrix_entry, ite_true] at he
  exact sub_right_injective he

/-- The common diagonal coefficient `a_n`. -/
def weightedResonantA (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : ℂ := weightedCorrectionMatrix hp w φ n z hz h 0 0

/-- The upper off-diagonal coefficient `b_n⁺`. -/
def weightedResonantBPlus (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : ℂ := weightedCorrectionMatrix hp w φ n z hz h 0 1

/-- The lower off-diagonal coefficient `b_n⁻`. -/
def weightedResonantBMinus (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : ℂ := weightedCorrectionMatrix hp w φ n z hz h 1 0

/-- The matrix form displayed immediately after Lemma 6.7. -/
theorem weightedResonantMatrix_form (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantMatrix hp w φ n z hz h =
      !![z - (Real.pi : ℂ) * n - weightedResonantA hp w φ n z hz h, -weightedResonantBPlus hp w φ n z hz h;
        -weightedResonantBMinus hp w φ n z hz h, z - (Real.pi : ℂ) * n - weightedResonantA hp w φ n z hz h] := by
  ext i j
  rw [weightedResonantMatrix_entry]
  change (if i = j then z - (Real.pi : ℂ) * n else 0) - weightedCorrectionMatrix hp w φ n z hz h i j = _
  fin_cases i <;> fin_cases j <;>
    simp [weightedResonantA, weightedResonantBPlus, weightedResonantBMinus, weightedCorrectionMatrix_diagonal_eq]

end NLS.ZakharovShabat
