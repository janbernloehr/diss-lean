import NLS.ZakharovShabat.ResonantParityExpansion

/-!
# Convergent scalar series for the resonant coefficients

The unwanted component-parity terms vanish individually. Continuous testing
of the actual even Neumann series gives the odd series for `a_n` and the
strictly positive even series for both off-diagonal Fourier remainders.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem weightedResonantA_even_term_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j : ℕ) :
    resonantCoordinates w.toWeight n
      ((((weightedPotentialInverse hp w φ n z hz)^2)^j) (weightedResonantSource hp w φ n 1)) 1 = 0 := by
  rw [resonantCoordinates_one, weightedPotentialInverse_even_snd_eq_zero hp w φ n z hz _
    (weightedResonantSource_one_snd_eq_zero hp w φ n)]
  rfl

theorem weightedResonantBPlus_odd_term_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j : ℕ) :
    resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
      ((((weightedPotentialInverse hp w φ n z hz)^2)^j) (weightedResonantSource hp w φ n 0))) 1 = 0 := by
  rw [resonantCoordinates_one, weightedPotentialInverse_snd_eq_zero hp w φ n z hz _
    (weightedPotentialInverse_even_fst_eq_zero hp w φ n z hz _ (weightedResonantSource_zero_fst_eq_zero hp w φ n) j)]
  rfl

theorem weightedResonantBMinus_odd_term_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j : ℕ) :
    resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
      ((((weightedPotentialInverse hp w φ n z hz)^2)^j) (weightedResonantSource hp w φ n 1))) 0 = 0 := by
  rw [resonantCoordinates_zero, weightedPotentialInverse_fst_eq_zero hp w φ n z hz _
    (weightedPotentialInverse_even_snd_eq_zero hp w φ n z hz _ (weightedResonantSource_one_snd_eq_zero hp w φ n) j)]
  rfl

/-- The source diagonal is the sum of its odd Neumann terms. -/
theorem weightedResonantA_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    HasSum (fun j : ℕ => resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
      ((((weightedPotentialInverse hp w φ n z hz)^2)^j) (weightedResonantSource hp w φ n 1))) 1)
      (weightedResonantA hp w φ n z hz h) := by
  let L : WeightedCoeffPair w.toWeight p →L[ℂ] ℂ := (ContinuousLinearMap.proj 1).comp
    ((resonantCoordinates w.toWeight n).comp (weightedPotentialInverse hp w φ n z hz))
  have hs := SquaredNeumann.evenSeries_hasSum_apply _ _ (weightedEvenCorrection_hasSum hp w φ n z hz h)
    L (weightedResonantSource hp w φ n 1)
  rw [weightedResonantA_parity]
  simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, weightedResonantEvenVector] using hs

/-- The positive Fourier remainder is the sum of strictly positive even Neumann terms. -/
theorem weightedResonantBPlus_remainder_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    HasSum (fun j : ℕ => resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
      (weightedPotentialInverse hp w φ n z hz
        ((((weightedPotentialInverse hp w φ n z hz)^2)^j) (weightedResonantSource hp w φ n 0)))) 1)
      (weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n)) := by
  let T := weightedPotentialInverse hp w φ n z hz
  let L : WeightedCoeffPair w.toWeight p →L[ℂ] ℂ := (ContinuousLinearMap.proj 1).comp
    ((resonantCoordinates w.toWeight n).comp (T.comp T))
  have hs := SquaredNeumann.evenSeries_hasSum_apply _ _ (weightedEvenCorrection_hasSum hp w φ n z hz h)
    L (weightedResonantSource hp w φ n 0)
  rw [weightedResonantBPlus_remainder]
  simpa only [L, T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, weightedResonantEvenVector] using hs

/-- The negative Fourier remainder is the sum of strictly positive even Neumann terms. -/
theorem weightedResonantBMinus_remainder_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    HasSum (fun j : ℕ => resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
      (weightedPotentialInverse hp w φ n z hz
        ((((weightedPotentialInverse hp w φ n z hz)^2)^j) (weightedResonantSource hp w φ n 1)))) 0)
      (weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))) := by
  let T := weightedPotentialInverse hp w φ n z hz
  let L : WeightedCoeffPair w.toWeight p →L[ℂ] ℂ := (ContinuousLinearMap.proj 0).comp
    ((resonantCoordinates w.toWeight n).comp (T.comp T))
  have hs := SquaredNeumann.evenSeries_hasSum_apply _ _ (weightedEvenCorrection_hasSum hp w φ n z hz h)
    L (weightedResonantSource hp w φ n 1)
  rw [weightedResonantBMinus_remainder]
  simpa only [L, T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, weightedResonantEvenVector] using hs

end NLS.ZakharovShabat
