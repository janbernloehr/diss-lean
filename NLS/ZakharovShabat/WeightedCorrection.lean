import NLS.FunctionalAnalysis.ConjugatedSquaredNeumann
import NLS.ZakharovShabat.WeightedContraction

/-!
# The Section 6 squared Neumann inverse

The shifted small-square estimate gives a bounded two-sided inverse of `Id-T_n`
on the original weighted space. The smallness condition is available locally
uniformly for large frequencies by `WeightedContraction`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The algebraic conjugation of the square is exactly the operator estimated in Lemma 6.5. -/
theorem conjugate_weightedPotentialInverse_sq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    (w.pairModulation n).conjContinuousAlgEquiv (weightedPotentialInverse hp w φ n z hz ^ 2) =
      weightedPotentialSquareInShift hp w φ n z hz := by
  ext f
  rfl

/-- The inverse of `Id-T_n²`, transported from the source's shifted norm. -/
def weightedEvenCorrection (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  SquaredNeumann.conjugateEvenCorrection (w.pairModulation n) (weightedPotentialInverse hp w φ n z hz)
    (by simpa only [conjugate_weightedPotentialInverse_sq] using h)

/-- The even correction is an actual convergent Neumann series on the original weighted space. -/
theorem weightedEvenCorrection_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    HasSum (fun j : ℕ => (weightedPotentialInverse hp w φ n z hz ^ 2) ^ j)
      (weightedEvenCorrection hp w φ n z hz h) := SquaredNeumann.conjugateEvenCorrection_hasSum _ _ _

/-- The source's `T̂_n=(Id-T_n)⁻¹`, defined from its small shifted square. -/
def weightedCorrection (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  SquaredNeumann.conjugateCorrection (w.pairModulation n) (weightedPotentialInverse hp w φ n z hz)
    (by simpa only [conjugate_weightedPotentialInverse_sq] using h)

/-- The displayed squared Neumann factorization on the original weighted space. -/
theorem weightedCorrection_formula (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedCorrection hp w φ n z hz h =
      (1 + weightedPotentialInverse hp w φ n z hz) * weightedEvenCorrection hp w φ n z hz h :=
  SquaredNeumann.conjugateCorrection_eq _ _ _

theorem weightedEvenCorrection_left (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedEvenCorrection hp w φ n z hz h * (1 - weightedPotentialInverse hp w φ n z hz ^ 2) = 1 :=
  SquaredNeumann.conjugateEvenCorrection_mul _ _ _

theorem weightedEvenCorrection_right (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (1 - weightedPotentialInverse hp w φ n z hz ^ 2) * weightedEvenCorrection hp w φ n z hz h = 1 :=
  SquaredNeumann.mul_conjugateEvenCorrection _ _ _

/-- The inverse cancels the complementary perturbation on the left. -/
theorem weightedCorrection_left (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (a : WeightedCoeffPair w.toWeight p) :
    weightedCorrection hp w φ n z hz h (a - weightedPotentialInverse hp w φ n z hz a) = a :=
  SquaredNeumann.conjugateCorrection_left _ _ _ a

/-- The inverse solves the complementary perturbation equation. -/
theorem weightedCorrection_right (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (a : WeightedCoeffPair w.toWeight p) :
    weightedCorrection hp w φ n z hz h a -
      weightedPotentialInverse hp w φ n z hz (weightedCorrection hp w φ n z hz h a) = a :=
  SquaredNeumann.conjugateCorrection_right _ _ _ a

theorem weightedCorrection_unique (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (a b : WeightedCoeffPair w.toWeight p)
    (he : a - weightedPotentialInverse hp w φ n z hz a = b) :
    a = weightedCorrection hp w φ n z hz h b := SquaredNeumann.conjugateCorrection_unique _ _ _ a b he

/-- The source uses both orders of `T_n` and `T̂_n`. -/
theorem weightedCorrection_commute (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (a : WeightedCoeffPair w.toWeight p) :
    weightedPotentialInverse hp w φ n z hz (weightedCorrection hp w φ n z hz h a) =
      weightedCorrection hp w φ n z hz h (weightedPotentialInverse hp w φ n z hz a) :=
  SquaredNeumann.conjugateCorrection_commute _ _ _ a

/-- The identity `Id + T_n T̂_n = T̂_n` used to solve the Q-equation. -/
theorem weightedCorrection_expand (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (a : WeightedCoeffPair w.toWeight p) :
    a + weightedPotentialInverse hp w φ n z hz (weightedCorrection hp w φ n z hz h a) =
      weightedCorrection hp w φ n z hz h a := by
  exact (sub_eq_iff_eq_add.mp (weightedCorrection_right hp w φ n z hz h a)).symm

/-- The weighted inverse restricts to the same unweighted inverse on their common inputs. -/
theorem forgetPairWeight_weightedCorrection (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (a : WeightedCoeffPair w.toWeight p) :
    w.forgetPairWeight (weightedCorrection hp w φ n z hz hw a) =
      weightedCorrection hp SpectralWeight.one (w.forgetPairWeight φ) n z hz h1 (w.forgetPairWeight a) := by
  apply weightedCorrection_unique hp SpectralWeight.one (w.forgetPairWeight φ) n z hz h1
  have he := congrArg w.forgetPairWeight (weightedCorrection_right hp w φ n z hz hw a)
  simpa only [map_sub, forgetPairWeight_potentialInverse] using he

end NLS.ZakharovShabat
