import NLS.ZakharovShabat.ResonantDiagonalSymmetry

/-!
# The resonant matrix in the dissertation's basis order

Equation (1.2), page 22, orders physical components as `(e_n⁻,e_n⁺)`.
The displayed matrix on page 40 instead uses `(e_n⁺,e_n⁻)`. Reversing both
matrix indices reconciles these conventions and preserves the determinant.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The reduced matrix in the source's ordered basis `(e_n⁺,e_n⁻)`. -/
def weightedSourceResonantMatrix (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => weightedResonantMatrix hp w φ n z hz h i.rev j.rev

/-- The source's exact displayed common-diagonal matrix, with its `b_n⁺` in the upper right. -/
theorem weightedSourceResonantMatrix_form (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedSourceResonantMatrix hp w φ n z hz h =
      !![z - (Real.pi : ℂ) * n - weightedResonantA hp w φ n z hz h, -weightedResonantBPlus hp w φ n z hz h;
        -weightedResonantBMinus hp w φ n z hz h, z - (Real.pi : ℂ) * n - weightedResonantA hp w φ n z hz h] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weightedSourceResonantMatrix, weightedResonantMatrix_form, Fin.rev]

/-- Reversing both basis indices preserves the resonant determinant. -/
theorem weightedSourceResonantMatrix_det (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (weightedSourceResonantMatrix hp w φ n z hz h).det = (weightedResonantMatrix hp w φ n z hz h).det := by
  rw [weightedSourceResonantMatrix_form, weightedResonantMatrix_form]
  simp [Matrix.det_fin_two, mul_comm]

/-- The determinant criterion also holds in precisely the source's basis order. -/
theorem weighted_eigenvector_iff_source_resonant_det_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (∃ f : WeightedDomain w.toWeight p, f ≠ 0 ∧ weightedFreePencil w.toWeight z f = weightedDomainPotential hp w φ f) ↔
      (weightedSourceResonantMatrix hp w φ n z hz h).det = 0 := by
  rw [weightedSourceResonantMatrix_det]
  exact weighted_eigenvector_iff_resonant_det_zero hp w φ n z hz h

end NLS.ZakharovShabat
