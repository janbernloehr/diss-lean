import NLS.SequenceSpaces.SignedSobolevWeight

/-! Exact signed target weights for square-root-decaying endpoint coordinates. -/
noncomputable section
namespace NLS.Weight

theorem positive_rpow_neg_le_sobolev (r : ℝ) (hr : 0 ≤ r) (n : ℕ+) :
    (n:ℝ)^(-r) ≤ (2:ℝ)^r*sobolev (-r) (n:ℤ) := by
  have hn : (0:ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt n.pos)
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 1+n)
    (by linarith : (1:ℝ)+n ≤ 2*n) (neg_nonpos.mpr hr)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hn.le] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) r)
  rw [← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2),add_neg_cancel,Real.rpow_zero,one_mul] at hm
  simpa only [sobolev_apply,Int.cast_natCast,abs_of_pos hn] using hm

theorem signed_endpoint_mul_le (r : ℝ) (hr : 0 ≤ r) (n : ℕ+) (z : ℂ) (C W B : ℝ)
    (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hz : ‖z‖ ≤ (C/Real.sqrt (n:ℕ))*W)
    (hB : sobolev (-r) (n:ℤ)*W ≤ B) :
    ‖(signedSobolev (1/2-r) (n:ℤ):ℂ)*z‖ ≤ (2:ℝ)^r*C*B := by
  have hn : (0:ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt n.pos)
  have hw : signedSobolev (1/2-r) (n:ℤ)=Real.sqrt (n:ℕ)*(n:ℝ)^(-r) := by
    simp only [signedSobolev,Int.cast_natCast,abs_of_pos hn,max_eq_right hn1]
    rw [sub_eq_add_neg,Real.rpow_add hn,← Real.sqrt_eq_rpow]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((signedSobolev (1/2-r)).positive _),hw]
  calc
    _ ≤ (Real.sqrt (n:ℕ)*(n:ℝ)^(-r))*((C/Real.sqrt (n:ℕ))*W) :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    _ = (n:ℝ)^(-r)*C*W := by field_simp [ne_of_gt (Real.sqrt_pos.mpr hn)]
    _ ≤ ((2:ℝ)^r*sobolev (-r) (n:ℤ))*C*W :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (positive_rpow_neg_le_sobolev r hr n) hC) hW
    _ = ((2:ℝ)^r*C)*(sobolev (-r) (n:ℤ)*W) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)

end NLS.Weight
