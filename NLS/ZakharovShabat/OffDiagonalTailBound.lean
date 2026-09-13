import NLS.ZakharovShabat.OffDiagonalRegions
import NLS.ZakharovShabat.OffDiagonalUniformBound

/-!
# Actual off-diagonal bounds with both potential tails

The regional Hölder estimate is applied to the exact even vectors. One
neighborhood and cutoff work for every larger tail cutoff and every full strip.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The parameter-independent weighted remainder bound after the three-region split. -/
def offDiagonalTailBound (hp : p ≠ ⊤) (w : SpectralWeight) (d a : WeightedCoeff w.toWeight p)
    (N : ℕ) (n : ℤ) : ℝ :=
  (2 * ‖d‖) * (2 * ‖d‖ * ‖doubleReciprocalFarRow
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    (WeightedCoeff.weightEquiv w.toWeight p a) (N/2) n‖ +
    ‖WeightedCoeff.fourierTail w.toWeight N d‖ * ‖doubleReciprocalNearRow
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    (WeightedCoeff.weightEquiv w.toWeight p a) N n‖)

theorem offDiagonalTailBound_nonneg (hp : p ≠ ⊤) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) : 0 ≤ offDiagonalTailBound hp w d a N n := by
  unfold offDiagonalTailBound
  positivity

/-- The source physical series obeys the refined bound whenever the input has its even-vector bound. -/
theorem weighted_norm_tsum_offDiagonal_tail_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (hf : w.shiftedNorm n f ≤ 2 * ‖d‖) :
    w (2*n) * ‖∑' l : ℤ, ∑' k : ℤ, d.val (n+l) * a.val (l+k) *
      complementarySymbol n z l * complementarySymbol n z k * f.val k‖ ≤ offDiagonalTailBound hp w d a N n := by
  have hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hqt := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have h := norm_tsum_offDiagonal_regions_le hq hqt w d a f N n hn z hz
  rw [(summable_norm_weightedOffDiagonalTerm hq w d a f n z hz).of_norm.tsum_prod,
    tsum_weightedOffDiagonalTerm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.positive _).le] at h
  exact h.trans (mul_le_mul_of_nonneg_right hf (by positivity))

/-- The negative coefficient retains the tails of both potential components. -/
theorem weightedResonantBMinus_remainder_tail_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    w (2*n) * ‖weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))‖ ≤
      offDiagonalTailBound hp w (w.reflection φ.fst) φ.snd N n := by
  have hf : w.shiftedNorm n (w.reflection (weightedResonantEvenVector hp w φ n z hz h 1).fst) ≤
      2 * ‖w.reflection φ.fst‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact (shiftedNorm_reflected_fst_le_pair w n _).trans
      (shiftedPairNorm_evenVector_one_le hp w φ n z hz h hh)
  have ht := weighted_norm_tsum_offDiagonal_tail_le hp hp1 w (w.reflection φ.fst) φ.snd
    (w.reflection (weightedResonantEvenVector hp w φ n z hz h 1).fst) N n hn z hz hf
  rw [weightedResonantBMinus_remainder_eq_tsum]
  simpa only [SpectralWeight.reflection_apply] using ht

/-- The positive coefficient has the matching refined bound with the components exchanged. -/
theorem weightedResonantBPlus_remainder_tail_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    w (2*n) * ‖weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n)‖ ≤
      offDiagonalTailBound hp w φ.snd (w.reflection φ.fst) N n := by
  have hf := (shiftedNorm_snd_le_pair w n (weightedResonantEvenVector hp w φ n z hz h 0)).trans
    (shiftedPairNorm_evenVector_zero_le hp w φ n z hz h hh)
  have ht := weighted_norm_tsum_offDiagonal_tail_le hp hp1 w φ.snd (w.reflection φ.fst)
    (weightedResonantEvenVector hp w φ n z hz h 0).snd N n hn z hz hf
  rw [weightedResonantBPlus_remainder_eq_tsum]
  simpa only [SpectralWeight.reflection_apply] using ht

/-- One cutoff works for both analytic remainders and for every larger choice of tail cutoff. -/
theorem exists_uniform_offDiagonalTailBound (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ _hz : z ∈ resonantStrip n,
        w (2*n) * ‖weightedResonantBMinusExtension hp w ψ n z - ψ.fst.val (-(2*n))‖ ≤
          offDiagonalTailBound hp w (w.reflection ψ.fst) ψ.snd N n ∧
        w (2*n) * ‖weightedResonantBPlusExtension hp w ψ n z - ψ.snd.val (2*n)‖ ≤
          offDiagonalTailBound hp w ψ.snd (w.reflection ψ.fst) N n := by
  obtain ⟨N₀, _, U, ho, hc, hφ, h0, _, hb⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨max 2 N₀, le_max_left _ _, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN n hn z hz
  have hh := (hb ψ hψ n (by omega) z hz).1
  have h := hh.trans_lt (by norm_num : (1/2 : ℝ) < 1)
  rw [weightedResonantBMinusExtension_eq hp w ψ n z hz h, weightedResonantBPlusExtension_eq hp w ψ n z hz h]
  exact ⟨weightedResonantBMinus_remainder_tail_le hp hp1 w ψ N n hn z hz h hh,
    weightedResonantBPlus_remainder_tail_le hp hp1 w ψ N n hn z hz h hh⟩

end NLS.ZakharovShabat
