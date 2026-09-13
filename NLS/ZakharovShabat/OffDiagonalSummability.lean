import NLS.ZakharovShabat.OffDiagonalPairPower
import NLS.ZakharovShabat.OffDiagonalSup

/-!
# Lemma 6.8(ii): proof-consistent weighted off-diagonal summability

For every finite `p>1`, the actual weighted full-strip remainder suprema
have convergent `p`-power tails. Their sums obey the source pair-norm
estimate, locally uniformly and for every cutoff beyond one threshold.

We follow the `p`-power sum and full pair norm in the concluding estimate
on source page 43. The display on page 41 differs: it omits the left-hand
`p`-powers and writes the positive component in place of the pair norm.
The literal page-41 display is not asserted here.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A nonnegative high-frequency sequence below the regional majorant has a convergent power sum. -/
theorem summable_offDiagonal_dominated_tail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (hN : 2 ≤ N) (S : ℤ → ℝ)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ S n ∧ S n ≤ offDiagonalTailBound hp w d a N n) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (S n)^p.toReal else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then (S n)^p.toReal else 0) ≤
        ∑' n : ℤ, (offDiagonalTailBound hp w d a N n)^p.toReal := by
  have hs := (offDiagonalTailBound_summable_and_le hp hp1 w d a N hN).1
  have hnonneg (n : ℤ) : 0 ≤ (if N ≤ n.natAbs then (S n)^p.toReal else 0) := by
    split_ifs with hn
    · exact Real.rpow_nonneg (hb n hn).1 _
    · exact le_rfl
  have hle (n : ℤ) : (if N ≤ n.natAbs then (S n)^p.toReal else 0) ≤
      (offDiagonalTailBound hp w d a N n)^p.toReal := by
    split_ifs with hn
    · exact Real.rpow_le_rpow (hb n hn).1 (hb n hn).2 ENNReal.toReal_nonneg
    · exact Real.rpow_nonneg (offDiagonalTailBound_nonneg hp w d a N n) _
  have hactual := hs.of_nonneg_of_le hnonneg hle
  exact ⟨hactual, hactual.tsum_le_tsum hle hs⟩

/-- The negative remainder's actual supremum tail satisfies the weighted pair estimate. -/
theorem resonantBMinusSup_tail_summable_and_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 2 ≤ N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantBMinusRemainderSup hp w φ n ∧
      resonantBMinusRemainderSup hp w φ n ≤ offDiagonalTailBound hp w (w.reflection φ.fst) φ.snd N n) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) ≤
        offDiagonalSummationConstant p * ‖φ.fst‖^p.toReal *
          (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
            ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(2*p.toReal)) := by
  obtain ⟨hs, hsum⟩ := summable_offDiagonal_dominated_tail hp hp1 w (w.reflection φ.fst) φ.snd N hN _ hb
  exact ⟨hs, hsum.trans (offDiagonalTailBound_minus_sum_le_pair hp hp1 w φ N hN)⟩

/-- The positive remainder has the same estimate with the distinguished component exchanged. -/
theorem resonantBPlusSup_tail_summable_and_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 2 ≤ N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantBPlusRemainderSup hp w φ n ∧
      resonantBPlusRemainderSup hp w φ n ≤ offDiagonalTailBound hp w φ.snd (w.reflection φ.fst) N n) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0) ≤
        offDiagonalSummationConstant p * ‖φ.snd‖^p.toReal *
          (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
            ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(2*p.toReal)) := by
  obtain ⟨hs, hsum⟩ := summable_offDiagonal_dominated_tail hp hp1 w φ.snd (w.reflection φ.fst) N hN _ hb
  exact ⟨hs, hsum.trans (offDiagonalTailBound_plus_sum_le_pair hp hp1 w φ N hN)⟩

/-- The proof-consistent form of Lemma 6.8(ii): both weighted remainder sums obey the quantitative estimate locally uniformly. -/
theorem exists_uniform_offDiagonalSummability (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        (Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0) ∧
          (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0) ≤
            offDiagonalSummationConstant p * ‖ψ.fst‖^p.toReal *
              (‖ψ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
                ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^(2*p.toReal))) ∧
        (Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0) ∧
          (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0) ≤
            offDiagonalSummationConstant p * ‖ψ.snd‖^p.toReal *
              (‖ψ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
                ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^(2*p.toReal))) := by
  obtain ⟨N₀, hN₀, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_offDiagonalSup hp hp1 w φ
  refine ⟨N₀, hN₀, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN
  exact ⟨resonantBMinusSup_tail_summable_and_le hp hp1 w ψ N (hN₀.trans hN)
      (fun n hn => (hb ψ hψ N hN n hn).1),
    resonantBPlusSup_tail_summable_and_le hp hp1 w ψ N (hN₀.trans hN)
      (fun n hn => (hb ψ hψ N hN n hn).2.1)⟩

end NLS.ZakharovShabat
