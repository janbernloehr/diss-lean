import NLS.ZakharovShabat.ConjugateComplementary
import NLS.ZakharovShabat.WeightedCorrection
import NLS.ZakharovShabat.ResonantCoordinates

/-!
# Conjugation of the corrected potential

Uniqueness of `(Id-T_n)⁻¹` transfers signed conjugation to the actual Neumann
inverse. Resonant extraction and synthesis preserve the two-coordinate action.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Signed conjugation intertwines the actual inverses at conjugate spectral parameters. -/
theorem weightedConjugation_correction (hp : p ≠ ⊤) (w : SpectralWeight)
    (ε : ℂ) (hε : ε * ε = 1) (φ : WeightedCoeffPair w.toWeight p) (hφ : HasRealitySign w ε φ)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hc : ‖weightedPotentialSquareInShift hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1)
    (f : WeightedCoeffPair w.toWeight p) :
    weightedConjugation w.toWeight w.neg_eq ε (weightedCorrection hp w φ n z hz h f) =
      weightedCorrection hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc
        (weightedConjugation w.toWeight w.neg_eq ε f) := by
  apply weightedCorrection_unique
  rw [← weightedConjugation_potentialInverse hp w ε hε φ hφ n z hz,
    ← weightedConjugation_sub, weightedCorrection_right]

/-- Action of signed physical conjugation on the two resonant amplitudes. -/
def resonantConjugation (ε : ℂ) (c : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(starRingEnd ℂ) (c 1), ε * (starRingEnd ℂ) (c 0)]

@[simp] theorem resonantConjugation_zero (ε : ℂ) (c : Fin 2 → ℂ) :
    resonantConjugation ε c 0 = (starRingEnd ℂ) (c 1) := rfl
@[simp] theorem resonantConjugation_one (ε : ℂ) (c : Fin 2 → ℂ) :
    resonantConjugation ε c 1 = ε * (starRingEnd ℂ) (c 0) := rfl

theorem resonantCoordinates_conjugation (w : Weight) (hw : ∀ k, w (-k) = w k) (ε : ℂ)
    (n : ℤ) (f : WeightedCoeffPair w p) :
    resonantCoordinates w n (weightedConjugation w hw ε f) = resonantConjugation ε (resonantCoordinates w n f) := by
  funext i
  fin_cases i <;> simp

theorem weightedConjugation_synthesis (w : Weight) (hw : ∀ k, w (-k) = w k) (ε : ℂ)
    (n : ℤ) (c : Fin 2 → ℂ) :
    weightedConjugation w hw ε (resonantSynthesis (p := p) w n c) = resonantSynthesis w n (resonantConjugation ε c) := by
  apply weightedPair_ext <;> intro k
  · by_cases hk : k = -n <;> simp [hk, neg_eq_iff_eq_neg]
  · by_cases hk : k = n <;> simp [hk]

/-- Conjugation of the corrected potential, including the resonant derivative-domain lift. -/
theorem weightedConjugation_correctedSynthesis (hp : p ≠ ⊤) (w : SpectralWeight)
    (ε : ℂ) (hε : ε * ε = 1) (φ : WeightedCoeffPair w.toWeight p) (hφ : HasRealitySign w ε φ)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hc : ‖weightedPotentialSquareInShift hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1)
    (c : Fin 2 → ℂ) :
    weightedConjugation w.toWeight w.neg_eq ε
      (weightedCorrection hp w φ n z hz h
        (weightedDomainPotential hp w φ (resonantSynthesis w.toWeight.oneDerivative n c))) =
      weightedCorrection hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc
        (weightedDomainPotential hp w φ (resonantSynthesis w.toWeight.oneDerivative n (resonantConjugation ε c))) := by
  rw [weightedConjugation_correction hp w ε hε φ hφ,
    weightedConjugation_domainPotential hp w ε hε φ hφ, weightedConjugation_synthesis]

end NLS.ZakharovShabat
