import NLS.SequenceSpaces.ShiftedHilbertInverse

/-! # A multiplicative H¹ Fourier embedding

A variable shifted inverse weight and Cauchy–Schwarz bound the absolute
Fourier sum by the geometric mean of the L² and H¹ norms. The zero mode is
included, so the estimate applies to arbitrary periodic fields.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- Multiplicative absolute-summability bound, in squared form. -/
theorem norm_sobolevToL1_sq_le (a : WeightedCoeff (Weight.sobolev 1) 2) :
    ‖sobolevToL1CLM 2 (by simp) a‖^2 ≤ 12*‖sobolevToL2 (by norm_num : (0:ℝ) ≤ 1) a‖*‖a‖ := by
  let A := sobolevToL2 (by norm_num : (0:ℝ) ≤ 1) a
  by_cases hz : ‖A‖ = 0
  · have hA : A = 0 := norm_eq_zero.mp hz
    have ha : a = 0 := by
      apply Subtype.ext
      funext n
      have h := congrArg (fun c : Coeff 2 => c n) hA
      change A n = 0 at h
      simpa only [A,sobolevToL2_apply,zero_val] using h
    subst a
    simp
  have hA : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  let R : ℝ := ‖a‖/‖A‖
  have hR : 1 ≤ R := (one_le_div hA).mpr (norm_sobolevToL2_le (by norm_num) a)
  have hRA : R*‖A‖ = ‖a‖ := div_mul_cancel₀ _ hz
  let b : Coeff 2 := ((R-1:ℝ):ℂ) • A + weightEquiv (Weight.sobolev 1) 2 a
  have hb (n : ℤ) : b n = ((R+|(n:ℝ)| : ℝ):ℂ)*a.val n := by
    change ((R-1:ℝ):ℂ)*A n + weightEquiv (Weight.sobolev 1) 2 a n = _
    rw [weightEquiv_apply,Weight.sobolev_apply,Real.rpow_one]
    simp only [A,sobolevToL2_apply]
    push_cast
    ring
  have hbnorm : ‖b‖ ≤ 2*‖a‖ := by
    calc
      _ ≤ ‖((R-1:ℝ):ℂ) • A‖+‖weightEquiv (Weight.sobolev 1) 2 a‖ := norm_add_le _ _
      _ = (R-1)*‖A‖+‖a‖ := by
        rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr hR)]
        rfl
      _ ≤ _ := by nlinarith [norm_nonneg A]
  have he (n : ℤ) : ‖Coeff.shiftedInverse R hR n‖*‖b n‖ = ‖a.val n‖ := by
    rw [← norm_mul,Coeff.shiftedInverse_apply,hb,inv_mul_cancel_left₀]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith [abs_nonneg (n:ℝ)]))
  have hL : ‖sobolevToL1CLM 2 (by simp) a‖ ≤ ‖Coeff.shiftedInverse R hR‖*‖b‖ := by
    have h := lp.tsum_mul_le_mul_norm' (show (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal from Real.HolderConjugate.two_two)
      (Coeff.shiftedInverse R hR) b
    simp only [he] at h
    simpa only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal),
      ENNReal.toReal_one,Real.rpow_one,one_div_one,sobolevToL1CLM_apply] using h
  calc
    _ ≤ (‖Coeff.shiftedInverse R hR‖*‖b‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hL 2
    _ = ‖Coeff.shiftedInverse R hR‖^2*‖b‖^2 := mul_pow _ _ _
    _ ≤ (3/R)*(2*‖a‖)^2 := mul_le_mul
      (Coeff.norm_shiftedInverse_sq_le R hR) (pow_le_pow_left₀ (norm_nonneg _) hbnorm 2)
      (sq_nonneg _) (by positivity)
    _ = 12*‖A‖*‖a‖ := by
      dsimp only [R]
      have ha : ‖a‖ ≠ 0 := ne_of_gt (hA.trans_le (norm_sobolevToL2_le (by norm_num) a))
      field_simp; ring

/-- A convenient numerical form of the sharp multiplicative H¹ embedding. -/
theorem norm_sobolevToL1_le_geometric (a : WeightedCoeff (Weight.sobolev 1) 2) :
    ‖sobolevToL1CLM 2 (by simp) a‖ ≤
      4*Real.sqrt ‖sobolevToL2 (by norm_num : (0:ℝ) ≤ 1) a‖*Real.sqrt ‖a‖ := by
  have h := norm_sobolevToL1_sq_le a
  have hprod : 0 ≤ ‖sobolevToL2 (by norm_num : (0:ℝ) ≤ 1) a‖*‖a‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hs : (4*Real.sqrt ‖sobolevToL2 (by norm_num : (0:ℝ) ≤ 1) a‖*Real.sqrt ‖a‖)^2 =
      16*‖sobolevToL2 (by norm_num : (0:ℝ) ≤ 1) a‖*‖a‖ := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (norm_nonneg _),Real.sq_sqrt (norm_nonneg _)]
    norm_num
  have hn : 0 ≤ 4*Real.sqrt ‖sobolevToL2 (by norm_num : (0:ℝ) ≤ 1) a‖*Real.sqrt ‖a‖ := by positivity
  nlinarith [norm_nonneg (sobolevToL1CLM 2 (by simp) a)]

end NLS.WeightedCoeff
