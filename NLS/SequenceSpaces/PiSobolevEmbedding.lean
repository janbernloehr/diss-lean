import NLS.SequenceSpaces.LinearSpectralWeight
import NLS.SequenceSpaces.SobolevConstant

/-! # The source H¹ absolute Fourier-sum bound

The reciprocal π-normalized weight has squared ℓ² norm at most two.
Cauchy–Schwarz therefore gives the source constant √2 in H¹ → ℓ¹.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- The reciprocal source H¹ weight is square summable. -/
theorem inverse_piSobolev_memlp :
    Memℓp (fun n : ℤ => ((SpectralWeight.piSobolev 1 (by norm_num)) n : ℂ)⁻¹) 2 := by
  apply (Weight.inverse_sobolev_one_memlp (by norm_num : (1:ℝ≥0∞) < 2)).mono'
  intro n
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ((SpectralWeight.piSobolev 1 (by norm_num)).positive n),
    abs_of_pos ((Weight.sobolev 1).positive n)]
  apply inv_anti₀ ((Weight.sobolev 1).positive n)
  simpa [Weight.sobolev_apply] using SpectralWeight.bracket_le_of_hasLinearFactor
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) n

/-- The exact π normalization gives the numerical reciprocal bound used in Theorem 25.1. -/
theorem norm_inverse_piSobolev_sq_le :
    ‖inverseWeight (SpectralWeight.piSobolev 1 (by norm_num)).toWeight inverse_piSobolev_memlp‖^2 ≤ 2 := by
  let a := inverseWeight (SpectralWeight.piSobolev 1 (by norm_num)).toWeight inverse_piSobolev_memlp
  have he (n : ℤ) : ‖a n‖^2 = (1+Real.pi*|(n:ℝ)|)⁻¹^2 := by
    change ‖((SpectralWeight.piSobolev 1 (by norm_num) n : ℝ) : ℂ)⁻¹‖^2 = _
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ((SpectralWeight.piSobolev 1 (by norm_num)).positive n)]
    simp only [SpectralWeight.piSobolev_apply, Real.rpow_one, abs_mul,
      abs_of_pos Real.pi_pos, mul_comm]
  have hs : Summable (fun n : ℤ => (1+Real.pi*|(n:ℝ)|)⁻¹^2) := by
    have h := (lp.memℓp a).summable (by norm_num)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, he] using h
  have hn : ‖a‖^2 = ∑' n : ℤ, (1+Real.pi*|(n:ℝ)|)⁻¹^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, he] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) a
  change ‖a‖^2 ≤ 2
  rw [hn,hs.tsum_eq_add_tsum_ite 0]
  have heq (n : ℤ) :
      (if n = 0 then 0 else (1+Real.pi*|(n:ℝ)|)⁻¹^2) =
      Real.pi⁻¹^2*(if n = 0 then 0 else (Real.pi⁻¹+|(n:ℝ)|)^(-(2:ℝ))) := by
    split_ifs with h
    · simp
    rw [Real.rpow_neg (by positivity : 0 ≤ Real.pi⁻¹+|(n:ℝ)|),Real.rpow_two]
    field_simp
  simp only [heq,tsum_mul_left,Int.cast_zero,abs_zero,mul_zero,add_zero,inv_one,one_pow]
  have hb := ReciprocalSeries.tsum_int_shifted_rpow_le_integral
    (α := Real.pi⁻¹) (by positivity) (q := 2) (by norm_num)
  norm_num only [show (2:ℝ)-1=1 by norm_num,div_one,
    show (1:ℝ)-2 = -1 by norm_num,Real.rpow_neg_one,inv_inv] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg Real.pi⁻¹)
  have hid : Real.pi⁻¹^2*(2*Real.pi) = 2/Real.pi := by field_simp
  rw [hid] at hmul
  have hpi : 2/Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  linarith

/-- Source H¹ coefficients as an absolutely summable sequence. -/
def piSobolevToL1 : WeightedCoeff (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2 →L[ℂ] Coeff 1 :=
  toL1CLM _ inverse_piSobolev_memlp

@[simp] theorem piSobolevToL1_apply
    (a : WeightedCoeff (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2) (n : ℤ) :
    piSobolevToL1 a n = a.val n := by simp [piSobolevToL1]

/-- The sharp-enough squared absolute Fourier-sum estimate. -/
theorem norm_piSobolevToL1_sq_le
    (a : WeightedCoeff (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2) :
    ‖piSobolevToL1 a‖^2 ≤ 2*‖a‖^2 := by
  have h := norm_toL1CLM_le (SpectralWeight.piSobolev 1 (by norm_num)).toWeight inverse_piSobolev_memlp a
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right norm_inverse_piSobolev_sq_le (sq_nonneg ‖a‖))

end NLS.WeightedCoeff
