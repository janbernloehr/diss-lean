import NLS.ZakharovShabat.OffDiagonalHolder
import NLS.ZakharovShabat.ResonantAnalytic

/-!
# Locally uniform off-diagonal row bounds

One potential neighborhood and one cutoff provide both weighted row bounds
throughout every distant closed strip, for the actual coefficients and their
jointly analytic extensions.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The parameter-independent majorant for the negative off-diagonal remainder. -/
def resonantBMinusRemainderBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  (2 * ‖φ.fst‖^2) * ‖doubleReciprocalRow
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    (WeightedCoeff.weightEquiv w.toWeight p φ.snd) n‖

/-- The parameter-independent majorant for the positive off-diagonal remainder. -/
def resonantBPlusRemainderBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  (2 * ‖φ.snd‖^2) * ‖doubleReciprocalRow
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    (WeightedCoeff.weightEquiv w.toWeight p (w.reflection φ.fst)) n‖

/-- Both row bounds and agreement with the original coefficients hold on every distant full strip. -/
theorem exists_uniform_offDiagonalHolder (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1,
          weightedResonantBMinusExtension hp w ψ n z = weightedResonantBMinus hp w ψ n z hz h ∧
          weightedResonantBPlusExtension hp w ψ n z = weightedResonantBPlus hp w ψ n z hz h ∧
          w (2*n) * ‖weightedResonantBMinusExtension hp w ψ n z - ψ.fst.val (-(2*n))‖ ≤
            resonantBMinusRemainderBound hp w ψ n ∧
          w (2*n) * ‖weightedResonantBPlusExtension hp w ψ n z - ψ.snd.val (2*n)‖ ≤
            resonantBPlusRemainderBound hp w ψ n := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, _, hb⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N, hN, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ n hn z hz
  have hh := (hb ψ hψ n hn z hz).1
  have h := hh.trans_lt (by norm_num : (1/2 : ℝ) < 1)
  have hm := weightedResonantBMinusExtension_eq hp w ψ n z hz h
  have hp' := weightedResonantBPlusExtension_eq hp w ψ n z hz h
  refine ⟨h, hm, hp', ?_, ?_⟩
  · rw [hm]
    exact weightedResonantBMinus_remainder_le hp w ψ n z hz h hh
  · rw [hp']
    exact weightedResonantBPlus_remainder_le hp w ψ n z hz h hh

end NLS.ZakharovShabat
