import NLS.SequenceSpaces.WeightedHilbertInterpolation
import NLS.SequenceSpaces.WeightedFiniteBlock
import NLS.SequenceSpaces.WeightedFrequencyProjections

/-! Quantitative norms of Fourier bands N ≤ |k| < 2N in the
negative Sobolev scale. Both band edges are retained explicitly. -/
noncomputable section
namespace NLS.WeightedCoeff

def frequencyBand (w : Weight) (N : ℕ) (f : ℤ → ℂ) : WeightedCoeff w 2 :=
  finiteBlock w (Coeff.lowFrequencies (2*N) \ Coeff.lowFrequencies N) f

theorem frequencyBand_apply (w : Weight) (N : ℕ) (f : ℤ → ℂ) (k : ℤ) :
    (frequencyBand w N f).val k = if N ≤ k.natAbs ∧ k.natAbs < 2*N then f k else 0 := by
  simp only [frequencyBand, finiteBlock_val, Finset.mem_sdiff, Coeff.mem_lowFrequencies,
    not_lt]
  simp only [and_comm]

theorem frequencyBand_eq_projection_sub (w : Weight) (N : ℕ) (a : WeightedCoeff w 2) :
    frequencyBand w N a.val = frequencyProjection w (2*N) a-frequencyProjection w N a := by
  apply Subtype.ext
  funext k
  simp only [frequencyBand_apply, sub_val, frequencyProjection_apply]
  split_ifs <;> simp_all <;> omega

private theorem natAbs_cast (k : ℤ) : (k.natAbs:ℝ) = |(k:ℝ)| := by
  simpa only [Int.cast_natCast, Int.cast_abs] using
    congrArg (fun j : ℤ => (j:ℝ)) (Int.natCast_natAbs k)

theorem norm_frequencyBand_zero_le (r : ℝ) (hr : 0 ≤ r) (N : ℕ) (hN : 1 ≤ N)
    (a : WeightedCoeff (Weight.sobolev (-r)) 2) :
    ‖frequencyBand (Weight.sobolev 0) N a.val‖ ≤ ((2*N:ℕ):ℝ)^r*‖a‖ := by
  have hNp : (0:ℝ) < (2*N:ℕ) := by exact_mod_cast (show 0 < 2*N by omega)
  apply norm_le_of_weighted_coefficients _ _ _ _ _ (Real.rpow_nonneg hNp.le _)
  intro k
  rw [frequencyBand_apply, Weight.sobolev_zero_apply, one_mul]
  by_cases hk : N ≤ k.natAbs ∧ k.natAbs < 2*N
  · rw [if_pos hk]
    have hb : 1+|(k:ℝ)| ≤ ((2*N:ℕ):ℝ) := by
      rw [← natAbs_cast]
      exact_mod_cast (show 1+k.natAbs ≤ 2*N by omega)
    have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1+|(k:ℝ)|) hb hr
    have hweight : 1 ≤ ((2*N:ℕ):ℝ)^r*Weight.sobolev (-r) k := by
      calc
        1 = (1+|(k:ℝ)|)^r*(1+|(k:ℝ)|)^(-r) := by
          rw [← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hweight (norm_nonneg (a.val k))
  · rw [if_neg hk, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hNp.le _)
      (mul_nonneg ((Weight.sobolev (-r)).positive k).le (norm_nonneg _))

theorem norm_frequencyBand_minusOne_le (N : ℕ) (hN : 1 ≤ N) (f : ℤ → ℂ) :
    ‖frequencyBand (Weight.sobolev (-1)) N f‖ ≤
      (N:ℝ)^(-1:ℝ)*‖frequencyBand (Weight.sobolev 0) N f‖ := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply norm_le_of_weighted_coefficients _ _ _ _ _ (Real.rpow_nonneg hNp.le _)
  intro k
  simp only [frequencyBand_apply, Weight.sobolev_zero_apply, one_mul]
  by_cases hk : N ≤ k.natAbs ∧ k.natAbs < 2*N
  · rw [if_pos hk]
    have hb : (N:ℝ) ≤ 1+|(k:ℝ)| := by
      rw [← natAbs_cast]
      exact_mod_cast (show N ≤ 1+k.natAbs by omega)
    have hw : Weight.sobolev (-1) k ≤ (N:ℝ)^(-1:ℝ) :=
      Real.rpow_le_rpow_of_nonpos hNp hb (by norm_num)
    exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  · rw [if_neg hk, norm_zero, mul_zero, mul_zero]

end NLS.WeightedCoeff
