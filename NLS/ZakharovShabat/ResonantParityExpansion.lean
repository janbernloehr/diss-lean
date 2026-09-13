import NLS.ZakharovShabat.WeightedComponentParity
import NLS.ZakharovShabat.ResonantPotentialModes
import NLS.ZakharovShabat.ResonantDiagonalSymmetry

/-!
# The resonant coefficient expansions (1.14)–(1.15)

The diagonal receives only the odd part of the corrected potential. The
source `b_n⁺` and `b_n⁻` receive its even part, with leading Fourier
coefficients at physical frequencies `2n` and `-2n` respectively.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The vector `(Id-T_n²)⁻¹ Φe_n`, with the resonant mode in physical order. -/
def weightedResonantEvenVector (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (i : Fin 2) : WeightedCoeffPair w.toWeight p :=
  weightedEvenCorrection hp w φ n z hz h (weightedResonantSource hp w φ n i)

/-- The even correction of the negative basis source has only a positive component. -/
theorem weightedResonantEvenVector_zero_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (weightedResonantEvenVector hp w φ n z hz h 0).fst = 0 :=
  weightedEvenCorrection_fst_eq_zero hp w φ n z hz h _ (weightedResonantSource_zero_fst_eq_zero hp w φ n)

/-- The even correction of the positive basis source has only a negative component. -/
theorem weightedResonantEvenVector_one_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (weightedResonantEvenVector hp w φ n z hz h 1).snd = 0 :=
  weightedEvenCorrection_snd_eq_zero hp w φ n z hz h _ (weightedResonantSource_one_snd_eq_zero hp w φ n)

/-- Equation (1.14): the common diagonal is the odd part, tested on the source positive mode. -/
theorem weightedResonantA_parity (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantA hp w φ n z hz h =
      resonantCoordinates w.toWeight n
        (weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 1)) 1 := by
  unfold weightedResonantA
  rw [weightedCorrectionMatrix_diagonal_eq hp w φ n z hz h]
  change resonantCoordinates w.toWeight n (weightedCorrection hp w φ n z hz h (weightedResonantSource hp w φ n 1)) 1 = _
  rw [weightedCorrection_formula]
  change resonantCoordinates w.toWeight n (weightedResonantEvenVector hp w φ n z hz h 1 +
    weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 1)) 1 = _
  rw [map_add, Pi.add_apply, resonantCoordinates_one, weightedResonantEvenVector_one_snd]
  simp

/-- The positive off-diagonal source coefficient contains only the even correction. -/
theorem weightedResonantBPlus_even (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBPlus hp w φ n z hz h =
      resonantCoordinates w.toWeight n (weightedResonantEvenVector hp w φ n z hz h 0) 1 := by
  change resonantCoordinates w.toWeight n (weightedCorrection hp w φ n z hz h (weightedResonantSource hp w φ n 0)) 1 = _
  rw [weightedCorrection_formula]
  change resonantCoordinates w.toWeight n (weightedResonantEvenVector hp w φ n z hz h 0 +
    weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 0)) 1 = _
  rw [map_add, Pi.add_apply, resonantCoordinates_one, resonantCoordinates_one,
    weightedPotentialInverse_snd_eq_zero hp w φ n z hz _ (weightedResonantEvenVector_zero_fst hp w φ n z hz h)]
  simp

/-- The negative off-diagonal source coefficient contains only the even correction. -/
theorem weightedResonantBMinus_even (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBMinus hp w φ n z hz h =
      resonantCoordinates w.toWeight n (weightedResonantEvenVector hp w φ n z hz h 1) 0 := by
  change resonantCoordinates w.toWeight n (weightedCorrection hp w φ n z hz h (weightedResonantSource hp w φ n 1)) 0 = _
  rw [weightedCorrection_formula]
  change resonantCoordinates w.toWeight n (weightedResonantEvenVector hp w φ n z hz h 1 +
    weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 1)) 0 = _
  rw [map_add, Pi.add_apply, resonantCoordinates_zero, resonantCoordinates_zero,
    weightedPotentialInverse_fst_eq_zero hp w φ n z hz _ (weightedResonantEvenVector_one_snd hp w φ n z hz h)]
  simp

/-- The even vector minus its source is its second-iterate correction. -/
theorem weightedResonantEvenVector_sub_source (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (i : Fin 2) :
    weightedResonantEvenVector hp w φ n z hz h i - weightedResonantSource hp w φ n i =
      weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h i)) := by
  have he := congrArg (fun A : WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p =>
    A (weightedResonantSource hp w φ n i)) (weightedEvenCorrection_right hp w φ n z hz h)
  change weightedResonantEvenVector hp w φ n z hz h i -
    weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz
      (weightedResonantEvenVector hp w φ n z hz h i)) = weightedResonantSource hp w φ n i at he
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))

/-- Equation (1.15) for `b_n⁺`, with the source's positive Fourier coefficient. -/
theorem weightedResonantBPlus_remainder (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n) =
      resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 0))) 1 := by
  have he := congrArg (fun f => resonantCoordinates w.toWeight n f 1)
    (weightedResonantEvenVector_sub_source hp w φ n z hz h 0)
  simpa only [map_sub, Pi.sub_apply, resonantCoordinates_source_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero, ← weightedResonantBPlus_even] using he

/-- Equation (1.15) for `b_n⁻`; signed negative coefficients have physical frequency `-2n`. -/
theorem weightedResonantBMinus_remainder (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n)) =
      resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz (weightedResonantEvenVector hp w φ n z hz h 1))) 0 := by
  have he := congrArg (fun f => resonantCoordinates w.toWeight n f 0)
    (weightedResonantEvenVector_sub_source hp w φ n z hz h 1)
  simpa only [map_sub, Pi.sub_apply, resonantCoordinates_source_one, Matrix.cons_val_zero,
    ← weightedResonantBMinus_even] using he

end NLS.ZakharovShabat
