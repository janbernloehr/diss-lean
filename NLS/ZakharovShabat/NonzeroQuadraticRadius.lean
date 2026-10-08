import NLS.ZakharovShabat.QuadraticLocalizationRadius

/-! # Nonzero-index arithmetic for Proposition 26.1 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- At a nonzero signed index the exact threshold improves the source radius to 3/8. -/
theorem quadraticLocalizationRadius_le_three_eighths {P : ℝ} (hP : 0 ≤ P) (n : ℤ)
    (hn0 : n ≠ 0) (hn : 8*P^2 ≤ 1+|(n:ℝ)|) : quadraticLocalizationRadius P n ≤ 3/8 := by
  have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (show (1:ℝ) ≤ (n.natAbs:ℝ) by exact_mod_cast (show 1 ≤ n.natAbs by omega))
  have hb : 4*(1+|(n:ℝ)|) ≤ (1+|((2*n:ℤ):ℝ)|)^2 := by
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [sq_nonneg (|(n:ℝ)|-1)]
  have hs : (Real.sqrt 2*P)^2 ≤ ((1+|((2*n:ℤ):ℝ)|)/4)^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith
  have hl := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt 2*P)
    (by positivity : 0 ≤ (1+|((2*n:ℤ):ℝ)|)/4)).mp hs
  have ho : Real.sqrt 2*P/(1+|((2*n:ℤ):ℝ)|) ≤ (1/4:ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have ha := quadratic_threshold_diagonal_le n hn
  unfold quadraticLocalizationRadius
  linarith

/-- The source half-unit localization implies the square comparison needed at every odd level. -/
theorem spectral_point_sq_bounds (c ζ : ℝ) (hc : 3 ≤ |c|) (hζ : |ζ-c| ≤ 1/2) :
    (1+2*|c|)^2/2 ≤ 4*ζ^2 ∧ 4*ζ^2 ≤ (1+2*|c|)^2 := by
  have hl := abs_sub_abs_le_abs_sub c ζ
  rw [abs_sub_comm c ζ] at hl
  have hu := abs_add_le (ζ-c) c
  rw [sub_add_cancel] at hu
  have hlo : (|c|-1/2)^2 ≤ |ζ|^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hhi : |ζ|^2 ≤ (|c|+1/2)^2 :=
    pow_le_pow_left₀ (abs_nonneg ζ) (by linarith) 2
  rw [sq_abs] at hlo hhi
  constructor
  · nlinarith [mul_nonneg (abs_nonneg c) (sub_nonneg.mpr hc)]
  · nlinarith

/-- The printed two-sided spectral-power comparison, including m=0. -/
theorem spectral_point_even_power_bounds (n : ℤ) (hn0 : n ≠ 0) (ζ : ℝ)
    (hζ : |ζ-Real.pi*n| ≤ 1/2) (m : ℕ) :
    ((2:ℝ)⁻¹)^m*(1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m) ≤ 4^m*ζ^(2*m) ∧
      4^m*ζ^(2*m) ≤ (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m) := by
  have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (show (1:ℝ) ≤ (n.natAbs:ℝ) by exact_mod_cast (show 1 ≤ n.natAbs by omega))
  have hc : 3 ≤ |Real.pi*n| := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hb := spectral_point_sq_bounds (Real.pi*n) ζ hc hζ
  have he : 1+2*|Real.pi*n| = 1+|((2*n:ℤ):ℝ)*Real.pi| := by
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  rw [he] at hb
  have hl := pow_le_pow_left₀ (by positivity : 0 ≤ (1+|((2*n:ℤ):ℝ)*Real.pi|)^2/2) hb.1 m
  have hu := pow_le_pow_left₀ (by positivity : 0 ≤ 4*ζ^2) hb.2 m
  simp only [div_pow,mul_pow,← pow_mul] at hl hu
  refine ⟨?_,hu⟩
  simpa only [div_eq_mul_inv,inv_pow,mul_comm] using hl

end NLS.ZakharovShabat
