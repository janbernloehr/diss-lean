import NLS.SequenceSpaces.PositiveSobolevWeight
import Mathlib.Tactic

/-! The standard Sobolev minus-half weight cancels the square-root
index growth in Cartesian frequency estimates at positive indices. -/
noncomputable section
open Complex
namespace NLS.Weight

theorem sobolev_neg_half_positive_le (n : ℕ+) :
    sobolev (-1/2) ((n:ℕ):ℤ) ≤ 1/Real.sqrt (n:ℕ) := by
  have hn : (0:ℝ) < (n:ℕ) := by exact_mod_cast n.pos
  have h := Real.rpow_le_rpow_of_nonpos hn (by linarith : ((n:ℕ):ℝ) ≤ 1+(n:ℕ))
    (by norm_num : (-1/2:ℝ) ≤ 0)
  have he : ((n:ℕ):ℝ)^(-1/2:ℝ) = 1/Real.sqrt (n:ℕ) := by
    rw [show (-1/2:ℝ) = -(1/2) by ring,Real.rpow_neg hn.le,← Real.sqrt_eq_rpow,one_div]
  simpa only [sobolev_apply,Int.cast_natCast,abs_of_pos hn,he] using h

theorem norm_sobolev_neg_half_mul_le_of_frequency_bound (n : ℕ+) (z τ : ℂ)
    (C B A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hz : ‖z‖ ≤ (C/Real.sqrt (n:ℕ))*‖τ‖*A) (hτ : ‖τ‖ ≤ B*(n:ℝ)) :
    ‖(sobolev (-1/2) ((n:ℕ):ℤ):ℂ)*z‖ ≤ C*B*A := by
  have hn : (0:ℝ) < (n:ℕ) := by exact_mod_cast n.pos
  have hCB : 0 ≤ C/Real.sqrt (n:ℕ) := div_nonneg hC (Real.sqrt_nonneg _)
  have hz' : ‖z‖ ≤ (C/Real.sqrt (n:ℕ))*(B*(n:ℝ))*A :=
    hz.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ hCB) hA)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((sobolev (-1/2)).positive _)]
  calc
    _ ≤ (1/Real.sqrt (n:ℕ))*((C/Real.sqrt (n:ℕ))*(B*(n:ℝ))*A) :=
      mul_le_mul (sobolev_neg_half_positive_le n) hz' (norm_nonneg _) (by positivity)
    _ = (C*B*A)*((n:ℝ)/(Real.sqrt (n:ℕ)*Real.sqrt (n:ℕ))) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [Real.mul_self_sqrt hn.le,div_self hn.ne',mul_one]

theorem norm_positiveSobolev_neg_half_mul_le_of_frequency_bound (n : ℕ+) (z τ : ℂ)
    (C B A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hz : ‖z‖ ≤ (C/Real.sqrt (n:ℕ))*‖τ‖*A) (hτ : ‖τ‖ ≤ B*(n:ℝ)) :
    ‖(positiveSobolev (-1/2) ((n:ℕ):ℤ):ℂ)*z‖ ≤ C*B*A := by
  have hn : (0:ℝ) < (n:ℕ) := by exact_mod_cast n.pos
  have hCB : 0 ≤ C/Real.sqrt (n:ℕ) := div_nonneg hC (Real.sqrt_nonneg _)
  have hz' : ‖z‖ ≤ (C/Real.sqrt (n:ℕ))*(B*(n:ℝ))*A :=
    hz.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ hCB) hA)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((positiveSobolev (-1/2)).positive _)]
  calc
    _ ≤ (1/Real.sqrt (n:ℕ))*((C/Real.sqrt (n:ℕ))*(B*(n:ℝ))*A) :=
      mul_le_mul (positiveSobolev_neg_half_positive n).le hz' (norm_nonneg _) (by positivity)
    _ = (C*B*A)*((n:ℝ)/(Real.sqrt (n:ℕ)*Real.sqrt (n:ℕ))) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [Real.mul_self_sqrt hn.le,div_self hn.ne',mul_one]

end NLS.Weight
