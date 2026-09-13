import NLS.FunctionalAnalysis.ConjugatedNeumannBounds
import NLS.ZakharovShabat.WeightedCorrection

/-!
# Quantitative approximation of the actual even correction

The source shifted norm has inverse bound `(1-q)⁻¹`, where `q` is the norm
of the shifted square. At `q≤1/2`, the inverse bound is two and the error
after `m` even terms is at most `2·2⁻ᵐ` times the input shifted norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite sum of the first `m` even powers of the actual complementary potential operator. -/
def weightedEvenPartialSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (m : ℕ) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  ∑ j ∈ Finset.range m, (weightedPotentialInverse hp w φ n z hz ^ 2)^j

/-- The inverse bound in exactly the source's shifted norm. -/
theorem shiftedPairNorm_evenCorrection_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm n (weightedEvenCorrection hp w φ n z hz h f) ≤
      (1-‖weightedPotentialSquareInShift hp w φ n z hz‖)⁻¹ * w.shiftedPairNorm n f := by
  simpa only [SpectralWeight.shiftedPairNorm, weightedEvenCorrection, conjugate_weightedPotentialInverse_sq] using
    SquaredNeumann.norm_conjugateEvenCorrection_apply_le (w.pairModulation n)
      (weightedPotentialInverse hp w φ n z hz) (by simpa only [conjugate_weightedPotentialInverse_sq] using h) f

/-- Half-size contraction gives inverse bound two without any weight or pair-norm loss. -/
theorem shiftedPairNorm_evenCorrection_le_two (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm n (weightedEvenCorrection hp w φ n z hz h f) ≤ 2 * w.shiftedPairNorm n f := by
  simpa only [SpectralWeight.shiftedPairNorm, weightedEvenCorrection] using
    SquaredNeumann.norm_conjugateEvenCorrection_apply_le_two (w.pairModulation n)
      (weightedPotentialInverse hp w φ n z hz) (by simpa only [conjugate_weightedPotentialInverse_sq] using h)
      (by simpa only [conjugate_weightedPotentialInverse_sq] using hh) f

/-- The exact finite-series remainder for the actual weighted inverse. -/
theorem weightedEvenCorrection_sub_partialSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (m : ℕ) :
    weightedEvenCorrection hp w φ n z hz h - weightedEvenPartialSum hp w φ n z hz m =
      (weightedPotentialInverse hp w φ n z hz ^ 2)^m * weightedEvenCorrection hp w φ n z hz h :=
  SquaredNeumann.conjugateEvenCorrection_sub_sum _ _ _ m

/-- Geometric approximation error in the shifted norm. -/
theorem shiftedPairNorm_evenCorrection_sub_partialSum_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (m : ℕ) (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm n (weightedEvenCorrection hp w φ n z hz h f - weightedEvenPartialSum hp w φ n z hz m f) ≤
      (‖weightedPotentialSquareInShift hp w φ n z hz‖^m * (1-‖weightedPotentialSquareInShift hp w φ n z hz‖)⁻¹) *
        w.shiftedPairNorm n f := by
  simpa only [SpectralWeight.shiftedPairNorm, weightedEvenCorrection, weightedEvenPartialSum,
    sub_apply, conjugate_weightedPotentialInverse_sq] using
    SquaredNeumann.norm_conjugateEvenCorrection_sub_sum_apply_le (w.pairModulation n)
      (weightedPotentialInverse hp w φ n z hz) (by simpa only [conjugate_weightedPotentialInverse_sq] using h) m f

/-- The uniform half-contraction approximation error, including an empty partial sum. -/
theorem shiftedPairNorm_evenCorrection_sub_partialSum_le_half (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (m : ℕ) (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm n (weightedEvenCorrection hp w φ n z hz h f - weightedEvenPartialSum hp w φ n z hz m f) ≤
      (2 * (1/2 : ℝ)^m) * w.shiftedPairNorm n f := by
  simpa only [SpectralWeight.shiftedPairNorm, weightedEvenCorrection, weightedEvenPartialSum, sub_apply] using
    SquaredNeumann.norm_conjugateEvenCorrection_sub_sum_apply_le_half (w.pairModulation n)
      (weightedPotentialInverse hp w φ n z hz) (by simpa only [conjugate_weightedPotentialInverse_sq] using h)
      (by simpa only [conjugate_weightedPotentialInverse_sq] using hh) m f

end NLS.ZakharovShabat
