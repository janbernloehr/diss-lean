import NLS.ZakharovShabat.SobolevWKBSecondColumn

/-! # Relative multipliers in the leading WKB term

Finite geometric and exponential estimates control the actual frequency multiplier by its displacement from the free lattice.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat

/-- A finite geometric bound controls powers near one without choosing
any logarithm or excluding zero powers. -/
theorem norm_pow_sub_one_le_geometric (x : ℂ) (hx : ‖x‖ ≤ 2) (N : ℕ) :
    ‖x^N-1‖ ≤ ((2:ℝ)^N-1)*‖x-1‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have he : x^(N+1)-1 = x*(x^N-1)+(x-1) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have h := mul_le_mul hx ih (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    have htwo : (2:ℝ)^(N+1) = 2*2^N := by ring
    rw [htwo]
    linarith

/-- The oscillatory and inverse-frequency factors differ from their
free-lattice values by a controlled multiple of the actual displacement. -/
theorem norm_wkb_leading_relative_multiplier_sub_one_le
    (N : ℕ) (z ζ δ : ℂ) (hz : 1 ≤ ‖z‖) (he : z = ζ+δ) (hδ : ‖δ‖ ≤ 1) :
    ‖exp (I*δ)*(ζ/z)^N-1‖ ≤ (Real.exp 1*(2^N-1)+2)*‖δ‖ := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hratio : ζ/z-1 = -δ/z := by
    field_simp
    linear_combination -he
  have hsmall : ‖ζ/z-1‖ ≤ ‖δ‖ := by
    rw [hratio,norm_div,norm_neg]
    exact div_le_self (norm_nonneg _) hz
  have hx : ‖ζ/z‖ ≤ 2 := by
    have h := norm_le_norm_sub_add (ζ/z) 1
    rw [norm_one] at h
    linarith
  have hpow := (norm_pow_sub_one_le_geometric (ζ/z) hx N).trans
    (mul_le_mul_of_nonneg_left hsmall (by have hh : (1:ℝ) ≤ 2^N := one_le_pow₀ (by norm_num); linarith))
  have hi : ‖I*δ‖ ≤ 1 := by simpa only [norm_mul,norm_I,one_mul] using hδ
  have hexp : ‖exp (I*δ)‖ ≤ Real.exp 1 :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hi)
  have hexp1 : ‖exp (I*δ)-1‖ ≤ 2*‖δ‖ := by
    simpa only [norm_mul,norm_I,one_mul] using Complex.norm_exp_sub_one_le hi
  have halg : exp (I*δ)*(ζ/z)^N-1 = exp (I*δ)*((ζ/z)^N-1)+(exp (I*δ)-1) := by ring
  rw [halg]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hh := mul_le_mul hexp hpow (norm_nonneg _) (Real.exp_pos 1).le
  nlinarith

end NLS.ZakharovShabat
