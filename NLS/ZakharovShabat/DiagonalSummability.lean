import NLS.ZakharovShabat.DiagonalTailPower

/-!
# Lemma 6.8(i): diagonal summability in the source pair norm

For every finite `p>1`, the actual full-strip suprema are summable to the
power `p` beyond one locally uniform cutoff. The quantitative estimate uses
the unweighted pair norm and the source half-cutoff Fourier tail.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Taking an ordinary Fourier tail commutes with forgetting the spectral weight. -/
theorem toCoeff_fourierTail (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) (N : ℕ) :
    w.toCoeff (WeightedCoeff.fourierTail w.toWeight N a) = Coeff.fourierTail N (w.toCoeff a) := by
  ext k
  simp only [toCoeff_apply, WeightedCoeff.fourierTail_apply, Coeff.fourierTail_apply]

end NLS.SpectralWeight
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A component's tail at `N` is controlled by the source pair tail at `N/2`. -/
theorem norm_diagonal_componentTail_le (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    ‖Coeff.fourierTail N (w.toCoeff φ.snd)‖ ≤
      ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) (w.forgetPairWeight φ)‖ := by
  calc
    _ ≤ ‖Coeff.fourierTail (N/2) (w.toCoeff φ.snd)‖ :=
      Coeff.norm_fourierTail_antitone (ne_of_gt (zero_lt_one.trans_le Fact.out)) _ (Nat.div_le_self N 2)
    _ = ‖w.forgetWeight (WeightedCoeff.fourierTail w.toWeight (N/2) φ.snd)‖ := by
      rw [← w.toCoeff_fourierTail, w.norm_toCoeff_eq_norm_forgetWeight]
    _ ≤ ‖w.forgetPairWeight (weightedPairFourierTail w.toWeight (N/2) φ)‖ :=
      WithLp.norm_snd_le _ (w.forgetPairWeight (weightedPairFourierTail w.toWeight (N/2) φ))
    _ = _ := by rw [forgetPairWeight_fourierTail]

/-- The diagonal supremum's power series converges, so its `tsum` is an actual sum. -/
theorem summable_diagonalSup_tail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantDiagonalSup hp w φ n ∧
      resonantDiagonalSup hp w φ n ≤ resonantDiagonalBound hp w φ n) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) := by
  obtain ⟨_, _, _, _, v, hv, _⟩ := exists_diagonalSupTail hp hp1 w φ N hN hb
  have hP := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  apply ((lp.memℓp v).summable hP).congr
  intro n
  rw [hv]
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_of_nonneg (hb n h).1]
  · simp [Real.zero_rpow hP.ne']

/-- Lemma 6.8(i), with the unweighted source pair norm and its half-cutoff tail. -/
theorem diagonalSup_tail_sum_le_pair (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantDiagonalSup hp w φ n ∧
      resonantDiagonalSup hp w φ n ≤ resonantDiagonalBound hp w φ n) :
    (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) ≤
      diagonalSummationConstant p * ‖w.forgetPairWeight φ‖^p.toReal *
        (‖w.forgetPairWeight φ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) (w.forgetPairWeight φ)‖^p.toReal) := by
  apply (diagonalSup_tail_sum_le hp hp1 w φ N hN hb).trans
  have hf : ‖w.forgetWeight φ.fst‖ ≤ ‖w.forgetPairWeight φ‖ := WithLp.norm_fst_le _ (w.forgetPairWeight φ)
  have hg : ‖w.toCoeff φ.snd‖ ≤ ‖w.forgetPairWeight φ‖ := by
    rw [w.norm_toCoeff_eq_norm_forgetWeight]
    exact WithLp.norm_snd_le _ (w.forgetPairWeight φ)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hf ENNReal.toReal_nonneg)
      diagonalSummationConstant_nonneg
  · exact add_le_add
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) hg ENNReal.toReal_nonneg) (by positivity))
      (Real.rpow_le_rpow (norm_nonneg _) (norm_diagonal_componentTail_le w φ N) ENNReal.toReal_nonneg)
  · positivity
  · exact mul_nonneg diagonalSummationConstant_nonneg (by positivity)

/-- The source diagonal summability estimate holds locally uniformly for every larger cutoff. -/
theorem exists_uniform_diagonalSummability (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantDiagonalSup hp w ψ n)^p.toReal else 0) ∧
        (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w ψ n)^p.toReal else 0) ≤
          diagonalSummationConstant p * ‖w.forgetPairWeight ψ‖^p.toReal *
            (‖w.forgetPairWeight ψ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) +
              ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) (w.forgetPairWeight ψ)‖^p.toReal) := by
  obtain ⟨N₀, hN₀, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_resonantDiagonalSup hp w φ
  refine ⟨N₀, hN₀, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN
  have hbound (n : ℤ) (hn : N ≤ n.natAbs) :
      0 ≤ resonantDiagonalSup hp w ψ n ∧
      resonantDiagonalSup hp w ψ n ≤ resonantDiagonalBound hp w ψ n := ⟨(hb ψ hψ n (hN.trans hn)).1, (hb ψ hψ n (hN.trans hn)).2.1⟩
  exact ⟨summable_diagonalSup_tail hp hp1 w ψ N (by omega) hbound,
    diagonalSup_tail_sum_le_pair hp hp1 w ψ N (by omega) hbound⟩

end NLS.ZakharovShabat
