import NLS.ZakharovShabat.UniformDisplacementMajorant

/-! # Sharper corrected Section 6 cutoff estimates

The original source norms and spectral data are retained. The additive leading-tail
term is not removed; the refuted printed estimates are not asserted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual supremum estimate retains the Fourier tail at the full cutoff. -/
theorem norm_diagonal_componentTail_le_fullCutoff (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    ‖Coeff.fourierTail N (w.toCoeff φ.snd)‖ ≤
      ‖weightedPairFourierTail SpectralWeight.one.toWeight N (w.forgetPairWeight φ)‖ := by
  calc
    _ ≤ ‖Coeff.fourierTail N (w.toCoeff φ.snd)‖ :=
      Coeff.norm_fourierTail_antitone (ne_of_gt (zero_lt_one.trans_le Fact.out)) _ (le_refl N)
    _ = ‖w.forgetWeight (WeightedCoeff.fourierTail w.toWeight N φ.snd)‖ := by
      rw [← w.toCoeff_fourierTail, w.norm_toCoeff_eq_norm_forgetWeight]
    _ ≤ ‖w.forgetPairWeight (weightedPairFourierTail w.toWeight N φ)‖ :=
      WithLp.norm_snd_le _ (w.forgetPairWeight (weightedPairFourierTail w.toWeight N φ))
    _ = _ := by rw [forgetPairWeight_fourierTail]

/-- The actual supremum estimate retains the Fourier tail at the full cutoff. -/
theorem diagonalSup_tail_sum_le_pair_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantDiagonalSup hp w φ n ∧
      resonantDiagonalSup hp w φ n ≤ resonantDiagonalBound hp w φ n) :
    (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) ≤
      diagonalSummationConstant p * ‖w.forgetPairWeight φ‖^p.toReal *
        (‖w.forgetPairWeight φ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail SpectralWeight.one.toWeight N (w.forgetPairWeight φ)‖^p.toReal) := by
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
      (Real.rpow_le_rpow (norm_nonneg _) (norm_diagonal_componentTail_le_fullCutoff w φ N) ENNReal.toReal_nonneg)
  · positivity
  · exact mul_nonneg diagonalSummationConstant_nonneg (by positivity)

/-- The actual supremum estimate retains the Fourier tail at the full cutoff. -/
theorem norm_offDiagonal_componentTails_le_fullCutoff (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    ‖WeightedCoeff.fourierTail w.toWeight N φ.fst‖ ≤ ‖weightedPairFourierTail w.toWeight N φ‖ ∧
    ‖WeightedCoeff.fourierTail w.toWeight N φ.snd‖ ≤ ‖weightedPairFourierTail w.toWeight N φ‖ := by
  exact ⟨(w.norm_fourierTail_antitone φ.fst (le_refl N)).trans
      (WithLp.norm_fst_le _ (weightedPairFourierTail w.toWeight N φ)),
    (w.norm_fourierTail_antitone φ.snd (le_refl N)).trans
      (WithLp.norm_snd_le _ (weightedPairFourierTail w.toWeight N φ))⟩

/-- The actual supremum estimate retains the Fourier tail at the full cutoff. -/
theorem offDiagonalTailBound_minus_sum_le_pair_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : ℤ, (offDiagonalTailBound hp w (w.reflection φ.fst) φ.snd N n)^p.toReal) ≤
      offDiagonalSummationConstant p * ‖φ.fst‖^p.toReal *
        (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal)) := by
  have hd : ‖w.reflection φ.fst‖ ≤ ‖φ‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact WithLp.norm_fst_le _ φ
  have htd : ‖WeightedCoeff.fourierTail w.toWeight N (w.reflection φ.fst)‖ ≤
      ‖weightedPairFourierTail w.toWeight N φ‖ := by
    rw [w.norm_fourierTail_reflection]
    exact (norm_offDiagonal_componentTails_le_fullCutoff w φ N).1
  simpa only [LinearIsometryEquiv.norm_map] using
    offDiagonalTailBound_sum_le_of_norm_bounds hp hp1 w (w.reflection φ.fst) φ.snd N hN
      ‖φ‖ ‖weightedPairFourierTail w.toWeight N φ‖ (norm_nonneg _) (norm_nonneg _)
      hd (WithLp.norm_snd_le _ φ) htd (norm_offDiagonal_componentTails_le_fullCutoff w φ N).2

/-- The actual supremum estimate retains the Fourier tail at the full cutoff. -/
theorem offDiagonalTailBound_plus_sum_le_pair_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : ℤ, (offDiagonalTailBound hp w φ.snd (w.reflection φ.fst) N n)^p.toReal) ≤
      offDiagonalSummationConstant p * ‖φ.snd‖^p.toReal *
        (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal)) := by
  have ha : ‖w.reflection φ.fst‖ ≤ ‖φ‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact WithLp.norm_fst_le _ φ
  have hta : ‖WeightedCoeff.fourierTail w.toWeight N (w.reflection φ.fst)‖ ≤
      ‖weightedPairFourierTail w.toWeight N φ‖ := by
    rw [w.norm_fourierTail_reflection]
    exact (norm_offDiagonal_componentTails_le_fullCutoff w φ N).1
  exact offDiagonalTailBound_sum_le_of_norm_bounds hp hp1 w φ.snd (w.reflection φ.fst) N hN
    ‖φ‖ ‖weightedPairFourierTail w.toWeight N φ‖ (norm_nonneg _) (norm_nonneg _)
    (WithLp.norm_snd_le _ φ) ha (norm_offDiagonal_componentTails_le_fullCutoff w φ N).2 hta

/-- The actual supremum estimate retains the Fourier tail at the full cutoff. -/
theorem resonantBMinusSup_tail_summable_and_le_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 2 ≤ N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantBMinusRemainderSup hp w φ n ∧
      resonantBMinusRemainderSup hp w φ n ≤ offDiagonalTailBound hp w (w.reflection φ.fst) φ.snd N n) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) ≤
        offDiagonalSummationConstant p * ‖φ.fst‖^p.toReal *
          (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
            ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal)) := by
  obtain ⟨hs, hsum⟩ := summable_offDiagonal_dominated_tail hp hp1 w (w.reflection φ.fst) φ.snd N hN _ hb
  exact ⟨hs, hsum.trans (offDiagonalTailBound_minus_sum_le_pair_fullCutoff hp hp1 w φ N hN)⟩

/-- The actual supremum estimate retains the Fourier tail at the full cutoff. -/
theorem resonantBPlusSup_tail_summable_and_le_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 2 ≤ N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantBPlusRemainderSup hp w φ n ∧
      resonantBPlusRemainderSup hp w φ n ≤ offDiagonalTailBound hp w φ.snd (w.reflection φ.fst) N n) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0) ≤
        offDiagonalSummationConstant p * ‖φ.snd‖^p.toReal *
          (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
            ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal)) := by
  obtain ⟨hs, hsum⟩ := summable_offDiagonal_dominated_tail hp hp1 w φ.snd (w.reflection φ.fst) N hN _ hb
  exact ⟨hs, hsum.trans (offDiagonalTailBound_plus_sum_le_pair_fullCutoff hp hp1 w φ N hN)⟩

/-- The actual supremum estimate retains the Fourier tail at the full cutoff. -/
theorem diagonalSup_tail_sum_le_weightedPair_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantDiagonalSup hp w φ n ∧
      resonantDiagonalSup hp w φ n ≤ resonantDiagonalBound hp w φ n) :
    (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) ≤
      diagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight N φ‖^p.toReal) := by
  apply (diagonalSup_tail_sum_le_pair_fullCutoff hp hp1 w φ N hN hb).trans
  have hB := Real.rpow_le_rpow (norm_nonneg _) (w.norm_forgetPairWeight_le hp φ) (ENNReal.toReal_nonneg (a := p))
  have hT := Real.rpow_le_rpow (norm_nonneg _)
    (w.norm_forgetPairWeight_le hp (weightedPairFourierTail w.toWeight N φ)) (ENNReal.toReal_nonneg (a := p))
  rw [forgetPairWeight_fourierTail] at hT
  have hC := diagonalSummationConstant_nonneg (p := p)
  gcongr

end NLS.ZakharovShabat
