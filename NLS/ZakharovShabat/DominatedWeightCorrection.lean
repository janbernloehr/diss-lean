import NLS.SequenceSpaces.SpectralWeightInclusion
import NLS.ZakharovShabat.UnweightedResonantDeterminant

/-! # Resonant corrections agree under a dominated spectral weight

On a common contraction domain, uniqueness identifies the actual inverses
and every correction entry. The lower weight need not be the unit weight.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem weightedBaseToPair_inclusionPair (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (a : WeightedCoeffPair w.toWeight p) :
    weightedBaseToPair v (w.inclusionPair v h a) = weightedBaseToPair w a := by
  apply Prod.ext <;> ext k <;> simp

/-- The original complementary potential action commutes with lowering the weight. -/
theorem inclusionPair_potentialInverse (hp : p ≠ ⊤) (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w.toWeight p) :
    w.inclusionPair v h (weightedPotentialInverse hp w φ n z hz a) =
      weightedPotentialInverse hp v (w.inclusionPair v h φ) n z hz (w.inclusionPair v h a) := by
  apply weightedPair_ext <;> intro k <;>
    simp only [SpectralWeight.inclusionPair_fst,SpectralWeight.inclusionPair_snd,
      weightedPotentialInverse_fst,weightedPotentialInverse_snd,SpectralWeight.convolution_apply,
      complementaryScalarL1_apply]

/-- Uniqueness transfers the full squared-Neumann correction between the weights. -/
theorem inclusionPair_weightedCorrection (hp : p ≠ ⊤) (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hv : ‖weightedPotentialSquareInShift hp v (w.inclusionPair v h φ) n z hz‖ < 1)
    (a : WeightedCoeffPair w.toWeight p) :
    w.inclusionPair v h (weightedCorrection hp w φ n z hz hw a) =
      weightedCorrection hp v (w.inclusionPair v h φ) n z hz hv (w.inclusionPair v h a) := by
  apply weightedCorrection_unique hp v (w.inclusionPair v h φ) n z hz hv
  have he := congrArg (w.inclusionPair v h) (weightedCorrection_right hp w φ n z hz hw a)
  simpa only [map_sub,inclusionPair_potentialInverse] using he

/-- Resonant source vectors preserve their physical Fourier coefficients. -/
theorem inclusionPair_resonantSource (hp : p ≠ ⊤) (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (i : Fin 2) :
    w.inclusionPair v h (weightedResonantSource hp w φ n i) =
      weightedResonantSource hp v (w.inclusionPair v h φ) n i := by
  fin_cases i <;> apply weightedPair_ext <;> intro k <;> simp

/-- Every actual analytic correction entry agrees on the common contraction domain. -/
theorem weightedCorrectionEntryExtension_inclusion (hp : p ≠ ⊤)
    (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hv : ‖weightedPotentialSquareInShift hp v (w.inclusionPair v h φ) n z hz‖ < 1)
    (i j : Fin 2) :
    weightedCorrectionEntryExtension hp w φ n z i j =
      weightedCorrectionEntryExtension hp v (w.inclusionPair v h φ) n z i j := by
  have he := inclusionPair_weightedCorrection hp w v h φ n z hz hw hv (weightedResonantSource hp w φ n j)
  rw [inclusionPair_resonantSource] at he
  simp only [weightedCorrectionEntryExtension,weightedCorrectionExtension_eq hp w φ n z hz hw,
    weightedCorrectionExtension_eq hp v (w.inclusionPair v h φ) n z hz hv]
  rw [← he]
  fin_cases i <;> simp

/-- The resonant determinant is independent of a dominated weight whenever both inverses exist. -/
theorem resonantDeterminantExtension_inclusion (hp : p ≠ ⊤)
    (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hv : ‖weightedPotentialSquareInShift hp v (w.inclusionPair v h φ) n z hz‖ < 1) :
    resonantDeterminantExtension hp w φ n z =
      resonantDeterminantExtension hp v (w.inclusionPair v h φ) n z := by
  simp only [resonantDeterminantExtension,weightedResonantAExtension,
    weightedResonantBPlusExtension,weightedResonantBMinusExtension,
    weightedCorrectionEntryExtension_inclusion hp w v h φ n z hz hw hv]

end NLS.ZakharovShabat
