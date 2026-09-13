import NLS.ZakharovShabat.ConjugateCorrection
import NLS.ZakharovShabat.ResonantDiagonalSymmetry

/-!
# Lemma 6.7(ii), with the hypothesis used in its proof

For `φ*=εφ`, `ε²=1`, the common diagonal is real under conjugation of the
spectral parameter and the off-diagonal entries are exchanged with sign `ε`.
The reality hypothesis applies to both conclusions (source pages 40–41).
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem resonantConjugation_basis_one (ε : ℂ) :
    resonantConjugation ε (Pi.single 1 1) = Pi.single 0 1 := by
  funext i
  fin_cases i <;> simp

@[simp] theorem resonantConjugation_basis_zero (ε : ℂ) :
    resonantConjugation ε (Pi.single 0 1) = ε • Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp

/-- The corrected diagonal reality statement: retain `φ*=εφ` for `a_n` as in the source proof. -/
theorem weightedResonantA_conj (hp : p ≠ ⊤) (w : SpectralWeight)
    (ε : ℂ) (hε : ε * ε = 1) (φ : WeightedCoeffPair w.toWeight p) (hφ : HasRealitySign w ε φ)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hc : ‖weightedPotentialSquareInShift hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1) :
    weightedResonantA hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
      (starRingEnd ℂ) (weightedResonantA hp w φ n z hz h) := by
  have he := congrArg (resonantCoordinates w.toWeight n)
    (weightedConjugation_correctedSynthesis hp w ε hε φ hφ n z hz h hc (Pi.single 1 1))
  rw [resonantCoordinates_conjugation, resonantConjugation_basis_one] at he
  have he := congrFun he 0
  change (starRingEnd ℂ) (weightedCorrectionMatrix hp w φ n z hz h 1 1) =
    weightedCorrectionMatrix hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc 0 0 at he
  change weightedCorrectionMatrix hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc 0 0 =
    (starRingEnd ℂ) (weightedCorrectionMatrix hp w φ n z hz h 0 0)
  rw [weightedCorrectionMatrix_diagonal_eq hp w φ n z hz h]
  exact he.symm

/-- The off-diagonal reality identity, with the sign of the source potential type. -/
theorem weightedResonantBMinus_conj (hp : p ≠ ⊤) (w : SpectralWeight)
    (ε : ℂ) (hε : ε * ε = 1) (φ : WeightedCoeffPair w.toWeight p) (hφ : HasRealitySign w ε φ)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hc : ‖weightedPotentialSquareInShift hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1) :
    weightedResonantBMinus hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
      ε * (starRingEnd ℂ) (weightedResonantBPlus hp w φ n z hz h) := by
  have he := congrArg (resonantCoordinates w.toWeight n)
    (weightedConjugation_correctedSynthesis hp w ε hε φ hφ n z hz h hc (Pi.single 0 1))
  simp only [resonantCoordinates_conjugation, resonantConjugation_basis_zero, map_smul] at he
  have he := congrFun he 0
  change (starRingEnd ℂ) (weightedCorrectionMatrix hp w φ n z hz h 1 0) =
    ε * weightedCorrectionMatrix hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc 0 1 at he
  have hm := congrArg (fun c : ℂ => ε * c) he
  simpa only [← mul_assoc, hε, one_mul, weightedResonantBMinus, weightedResonantBPlus] using hm.symm

/-- The source `b_n⁺` identity follows directly from the second physical component. -/
theorem weightedResonantBPlus_conj (hp : p ≠ ⊤) (w : SpectralWeight)
    (ε : ℂ) (hε : ε * ε = 1) (φ : WeightedCoeffPair w.toWeight p) (hφ : HasRealitySign w ε φ)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hc : ‖weightedPotentialSquareInShift hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1) :
    weightedResonantBPlus hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
      ε * (starRingEnd ℂ) (weightedResonantBMinus hp w φ n z hz h) := by
  have he := congrArg (resonantCoordinates w.toWeight n)
    (weightedConjugation_correctedSynthesis hp w ε hε φ hφ n z hz h hc (Pi.single 1 1))
  rw [resonantCoordinates_conjugation, resonantConjugation_basis_one] at he
  exact (congrFun he 1).symm

/-- On the real spectral axis the common diagonal has zero imaginary part for either reality type. -/
theorem weightedResonantA_im_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (ε : ℂ) (hε : ε * ε = 1) (φ : WeightedCoeffPair w.toWeight p) (hφ : HasRealitySign w ε φ)
    (n : ℤ) (x : ℝ) (hx : (x : ℂ) ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n (x : ℂ) hx‖ < 1) :
    (weightedResonantA hp w φ n (x : ℂ) hx h).im = 0 := by
  have hc : ‖weightedPotentialSquareInShift hp w φ n ((starRingEnd ℂ) (x : ℂ)) (conj_mem_resonantStrip hx)‖ < 1 := by
    simpa only [Complex.conj_ofReal] using h
  have he := weightedResonantA_conj hp w ε hε φ hφ n (x : ℂ) hx h hc
  simp only [Complex.conj_ofReal] at he
  have hi := congrArg Complex.im he
  rw [Complex.conj_im] at hi
  linarith

/-- Lemma 6.7(ii) holds with one locally uniform frequency cutoff over the full closed strips,
with the source reality hypothesis on both the diagonal and off-diagonal conclusions. -/
theorem exists_uniform_resonantConjugation (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1,
        ∃ hc : ‖weightedPotentialSquareInShift hp w ψ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1,
          ∀ ε : ℂ, ε * ε = 1 → HasRealitySign w ε ψ →
            weightedResonantA hp w ψ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
              (starRingEnd ℂ) (weightedResonantA hp w ψ n z hz h) ∧
            weightedResonantBPlus hp w ψ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
              ε * (starRingEnd ℂ) (weightedResonantBMinus hp w ψ n z hz h) := by
  obtain ⟨N, hN, U, ho, hv, hφ, h0, _, hb⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N, hN, U, ho, hv, hφ, h0, ?_⟩
  intro ψ hψ n hn z hz
  have h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1 :=
    ((hb ψ hψ n hn z hz).1).trans_lt (by norm_num)
  have hc : ‖weightedPotentialSquareInShift hp w ψ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1 :=
    ((hb ψ hψ n hn ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)).1).trans_lt (by norm_num)
  exact ⟨h, hc, fun ε hε hr => ⟨weightedResonantA_conj hp w ε hε ψ hr n z hz h hc,
    weightedResonantBPlus_conj hp w ε hε ψ hr n z hz h hc⟩⟩

end NLS.ZakharovShabat
