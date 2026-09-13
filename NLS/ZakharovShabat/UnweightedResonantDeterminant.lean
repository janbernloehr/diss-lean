import NLS.ZakharovShabat.ResonantDeterminantAnalytic
import NLS.ZakharovShabat.UnweightedEvenCorrection

/-!
# The weighted determinant and the original periodic spectrum

Uniqueness of the complementary inverse identifies the weighted and unit-weight
corrections on their common contraction domain. Resonant extraction preserves
physical Fourier coefficients, so the scalar determinants agree exactly.
The uniform square estimate supplies both contractions on one neighborhood.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Unit-weight realization after forgetting a weight is the original coefficient pair. -/
theorem unitBaseEquiv_forgetPairWeight (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    unitBaseEquiv (w.forgetPairWeight φ) = weightedBaseToPair w φ := by
  apply Prod.ext <;> ext k <;> simp

/-- Every actual correction entry is unchanged by forgetting the weight. -/
theorem weightedCorrectionEntryExtension_forget (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (i j : Fin 2) :
    weightedCorrectionEntryExtension hp w φ n z i j =
      weightedCorrectionEntryExtension hp SpectralWeight.one (w.forgetPairWeight φ) n z i j := by
  have he := forgetPairWeight_weightedCorrection hp w φ n z hz hw h1 (weightedResonantSource hp w φ n j)
  rw [forgetPairWeight_resonantSource] at he
  simp only [weightedCorrectionEntryExtension, weightedCorrectionExtension_eq hp w φ n z hz hw,
    weightedCorrectionExtension_eq hp SpectralWeight.one (w.forgetPairWeight φ) n z hz h1]
  rw [← he]
  fin_cases i <;> simp

/-- The weighted and unweighted scalar determinants coincide on their common domain. -/
theorem resonantDeterminantExtension_forget (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1) :
    resonantDeterminantExtension hp w φ n z =
      resonantDeterminantExtension hp SpectralWeight.one (w.forgetPairWeight φ) n z := by
  simp only [resonantDeterminantExtension, weightedResonantAExtension,
    weightedResonantBPlusExtension, weightedResonantBMinusExtension,
    weightedCorrectionEntryExtension_forget hp w φ n z hz hw h1]

/-- Weighted determinant zeros are exactly the original periodic spectral points. -/
theorem mem_periodicSpectrum_iff_weightedDeterminant_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1) :
    z ∈ periodicSpectrum hp (weightedBaseToPair w φ) ↔ resonantDeterminantExtension hp w φ n z = 0 := by
  rw [resonantDeterminantExtension_forget hp w φ n z hz hw h1, ← unitBaseEquiv_forgetPairWeight]
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    mem_periodicSpectrum_iff_resonantDeterminantExtension_zero hp (unitBaseEquiv (w.forgetPairWeight φ)) n z hz
      (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using h1)

/-- One neighborhood and cutoff identify the weighted determinant with the original spectrum on all distant strips. -/
theorem exists_uniform_weightedDeterminant_spectral_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        z ∈ periodicSpectrum hp (weightedBaseToPair w ψ) ↔ resonantDeterminantExtension hp w ψ n z = 0 := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,_,hb⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨hw,h1⟩ := hb ψ hψ n hn z hz
  rw [← norm_weightedPotentialSquareInShift_one hp] at h1
  exact mem_periodicSpectrum_iff_weightedDeterminant_zero hp w ψ n z hz
    (hw.trans_lt (by norm_num)) (h1.trans_lt (by norm_num))

end NLS.ZakharovShabat
