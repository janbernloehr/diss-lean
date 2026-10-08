import NLS.SequenceSpaces.SobolevConstant
import NLS.SequenceSpaces.SobolevHomogeneous

/-! # Shifted reciprocal Hilbert bounds, including the zero mode -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- The shifted inverse weight is dominated by the ordinary Sobolev inverse. -/
theorem shiftedInverse_memlp (R : ℝ) (hR : 1 ≤ R) :
    Memℓp (fun n : ℤ => ((R+|(n:ℝ)| : ℝ):ℂ)⁻¹) 2 := by
  apply (Weight.inverse_sobolev_one_memlp (by norm_num : (1:ℝ≥0∞) < 2)).mono'
  intro n
  simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,Weight.sobolev_apply,Real.rpow_one,
    abs_of_nonneg (by positivity : 0 ≤ 1+|(n:ℝ)|)]
  rw [abs_of_pos (by linarith [abs_nonneg (n:ℝ)] : 0 < R+|(n:ℝ)|)]
  exact inv_anti₀ (by positivity) (by linarith)

/-- A variable-shift inverse Fourier multiplier in ℓ². -/
def shiftedInverse (R : ℝ) (hR : 1 ≤ R) : Coeff 2 := ⟨_,shiftedInverse_memlp R hR⟩

@[simp] theorem shiftedInverse_apply (R : ℝ) (hR : 1 ≤ R) (n : ℤ) :
    shiftedInverse R hR n = ((R+|(n:ℝ)| : ℝ):ℂ)⁻¹ := rfl

/-- The full squared inverse-weight norm decays as 3/R for R≥1. -/
theorem norm_shiftedInverse_sq_le (R : ℝ) (hR : 1 ≤ R) :
    ‖shiftedInverse R hR‖^2 ≤ 3/R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he (n : ℤ) : ‖shiftedInverse R hR n‖^2 = (R+|(n:ℝ)|)^(-(2:ℝ)) := by
    simp only [shiftedInverse_apply,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith [abs_nonneg (n:ℝ)] : 0 < R+|(n:ℝ)|),
      Real.rpow_neg (by positivity : 0 ≤ R+|(n:ℝ)|),Real.rpow_two,inv_pow]
  have hs : Summable (fun n : ℤ => (R+|(n:ℝ)|)^(-(2:ℝ))) := by
    have h := (lp.memℓp (shiftedInverse R hR)).summable (by norm_num)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,he] using h
  have hn : ‖shiftedInverse R hR‖^2 = ∑' n : ℤ, (R+|(n:ℝ)|)^(-(2:ℝ)) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,he] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (shiftedInverse R hR)
  rw [hn,hs.tsum_eq_add_tsum_ite 0]
  have hb := ReciprocalSeries.tsum_int_shifted_rpow_le_integral (q := 2) hR0 (by norm_num)
  norm_num only [Int.cast_zero,abs_zero,add_zero,show (2:ℝ)-1=1 by norm_num,
    div_one,show (1:ℝ)-2 = -1 by norm_num,Real.rpow_neg_one] at hb ⊢
  have hi : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  rw [Real.rpow_neg hR0.le,Real.rpow_two,← inv_pow]
  rw [div_eq_mul_inv]
  nlinarith [sq_nonneg (R⁻¹),inv_nonneg.mpr hR0.le]

end NLS.Coeff
