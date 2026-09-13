import NLS.ZakharovShabat.ResonantEvenBounds

/-!
# Weight compatibility of the even inverse

The diagonal estimate of Lemma 6.8 needs unweighted potential norms. On the
simultaneous weighted/unit-weight contraction region, inverse uniqueness
identifies both even vectors and retains those smaller unweighted norms.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Unit-weight conjugation does not change the square's operator norm. -/
theorem norm_weightedPotentialSquareInShift_one (hp : p ≠ ⊤)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift hp SpectralWeight.one φ n z hz‖ =
      ‖(weightedPotentialInverse hp SpectralWeight.one φ n z hz).comp
        (weightedPotentialInverse hp SpectralWeight.one φ n z hz)‖ := by
  have hn (f : WeightedCoeffPair SpectralWeight.one.toWeight p) :
      ‖SpectralWeight.one.pairModulation n f‖ = ‖f‖ := SpectralWeight.shiftedPairNorm_one hp n f
  have hi (f : WeightedCoeffPair SpectralWeight.one.toWeight p) :
      ‖(SpectralWeight.one.pairModulation n).symm f‖ = ‖f‖ := by
    rw [← hn ((SpectralWeight.one.pairModulation n).symm f), ContinuousLinearEquiv.apply_symm_apply]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    change ‖SpectralWeight.one.pairModulation n
      (weightedPotentialInverse hp SpectralWeight.one φ n z hz
        (weightedPotentialInverse hp SpectralWeight.one φ n z hz ((SpectralWeight.one.pairModulation n).symm f)))‖ ≤ _
    rw [hn, ← hi f]
    simpa only [ContinuousLinearMap.comp_apply] using ContinuousLinearMap.le_opNorm
      ((weightedPotentialInverse hp SpectralWeight.one φ n z hz).comp
        (weightedPotentialInverse hp SpectralWeight.one φ n z hz)) ((SpectralWeight.one.pairModulation n).symm f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have h := ContinuousLinearMap.le_opNorm (weightedPotentialSquareInShift hp SpectralWeight.one φ n z hz)
      (SpectralWeight.one.pairModulation n f)
    change ‖SpectralWeight.one.pairModulation n
      (weightedPotentialInverse hp SpectralWeight.one φ n z hz
        (weightedPotentialInverse hp SpectralWeight.one φ n z hz
          ((SpectralWeight.one.pairModulation n).symm (SpectralWeight.one.pairModulation n f))))‖ ≤ _ at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hn, ContinuousLinearMap.comp_apply] using h

/-- Uniqueness for the actual even complementary equation. -/
theorem weightedEvenCorrection_unique (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (a b : WeightedCoeffPair w.toWeight p)
    (he : a - weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz a) = b) :
    a = weightedEvenCorrection hp w φ n z hz h b := by
  have hl := congrArg (fun A : WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p => A a)
    (weightedEvenCorrection_left hp w φ n z hz h)
  change weightedEvenCorrection hp w φ n z hz h
    (a - weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz a)) = a at hl
  rw [he] at hl
  exact hl.symm

/-- Forgetting the weight commutes with the even Neumann inverse whenever both are defined. -/
theorem forgetPairWeight_weightedEvenCorrection (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (a : WeightedCoeffPair w.toWeight p) :
    w.forgetPairWeight (weightedEvenCorrection hp w φ n z hz hw a) =
      weightedEvenCorrection hp SpectralWeight.one (w.forgetPairWeight φ) n z hz h1 (w.forgetPairWeight a) := by
  apply weightedEvenCorrection_unique hp SpectralWeight.one (w.forgetPairWeight φ) n z hz h1
  have hr := congrArg (fun A : WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p => A a)
    (weightedEvenCorrection_right hp w φ n z hz hw)
  change weightedEvenCorrection hp w φ n z hz hw a - weightedPotentialInverse hp w φ n z hz
    (weightedPotentialInverse hp w φ n z hz (weightedEvenCorrection hp w φ n z hz hw a)) = a at hr
  have hf := congrArg w.forgetPairWeight hr
  simpa only [map_sub, forgetPairWeight_potentialInverse] using hf

/-- The potential-source vectors retain their exact physical coefficients after forgetting the weight. -/
theorem forgetPairWeight_resonantSource (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (i : Fin 2) :
    w.forgetPairWeight (weightedResonantSource hp w φ n i) =
      weightedResonantSource hp SpectralWeight.one (w.forgetPairWeight φ) n i := by
  fin_cases i <;> apply weightedPair_ext <;> intro k <;> simp

/-- The actual even vectors agree in the unweighted realization. -/
theorem forgetPairWeight_resonantEvenVector (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (i : Fin 2) :
    w.forgetPairWeight (weightedResonantEvenVector hp w φ n z hz hw i) =
      weightedResonantEvenVector hp SpectralWeight.one (w.forgetPairWeight φ) n z hz h1 i := by
  simp only [weightedResonantEvenVector, forgetPairWeight_weightedEvenCorrection hp w φ n z hz hw h1,
    forgetPairWeight_resonantSource]

/-- The negative-mode vector is bounded using only the unweighted positive potential component. -/
theorem norm_forget_evenVector_zero_le_unweighted (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ ≤ 1/2) :
    ‖w.forgetPairWeight (weightedResonantEvenVector hp w φ n z hz hw 0)‖ ≤ 2 * ‖w.forgetWeight φ.snd‖ := by
  rw [forgetPairWeight_resonantEvenVector hp w φ n z hz hw h1]
  simpa only [SpectralWeight.shiftedPairNorm_one hp, SpectralWeight.forgetPairWeight_snd] using
    shiftedPairNorm_evenVector_zero_le hp SpectralWeight.one (w.forgetPairWeight φ) n z hz h1 hh

/-- The source positive-mode vector has the unweighted norm bound needed for Lemma 6.8(i). -/
theorem norm_forget_evenVector_one_le_unweighted (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ ≤ 1/2) :
    ‖w.forgetPairWeight (weightedResonantEvenVector hp w φ n z hz hw 1)‖ ≤ 2 * ‖w.forgetWeight φ.fst‖ := by
  rw [forgetPairWeight_resonantEvenVector hp w φ n z hz hw h1]
  simpa only [SpectralWeight.shiftedPairNorm_one hp, SpectralWeight.forgetPairWeight_fst] using
    shiftedPairNorm_evenVector_one_le hp SpectralWeight.one (w.forgetPairWeight φ) n z hz h1 hh

end NLS.ZakharovShabat

namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Ordinary coefficient realization and forgetting to unit weight have exactly the same norm. -/
theorem norm_toCoeff_eq_norm_forgetWeight (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) :
    ‖w.toCoeff a‖ = ‖w.forgetWeight a‖ := by
  have he : w.toCoeff a = WeightedCoeff.weightEquiv one.toWeight p (w.forgetWeight a) := by
    ext k
    rw [toCoeff_apply, WeightedCoeff.weightEquiv_apply, forgetWeight_apply]
    simp
  rw [he, ← WeightedCoeff.norm_eq]

end NLS.SpectralWeight
