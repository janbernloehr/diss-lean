import NLS.KdV.HillFreeGapContourGeometry

/-! # Quadratic high-energy separation in the Abelian contour scale -/
noncomputable section
open Set Complex
namespace NLS.KdV

theorem sq_le_freeHillValue_sub_of_two_mul_le (n k : ℕ) (hn : 1 ≤ n) (hk : 2*n ≤ k) :
    (k : ℝ)^2 ≤ freeHillValue k-freeHillValue n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : 2*(n : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 4*(n : ℝ)^2 ≤ (k : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (show 0 ≤ (k : ℝ)+2*n by positivity)]
  have hgap : 0 ≤ (k : ℝ)^2-(n : ℝ)^2 := by nlinarith
  have hpi : 2 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hm := mul_le_mul_of_nonneg_right hpi hgap
  dsimp only [freeHillValue]
  push_cast
  nlinarith

theorem norm_freeHill_Abelian_scale (n k : ℕ) (hn : 1 ≤ n) (hk : 2*n ≤ k) :
    ‖((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ)‖ =
      (freeHillValue k-freeHillValue n)/(n : ℝ) := by
  have hk1 : 1 ≤ k := by omega
  have hpos : 0 < freeHillValue k-freeHillValue n :=
    (sq_pos_of_pos (show (0 : ℝ) < k by exact_mod_cast (show 0 < k by omega))).trans_le
      (sq_le_freeHillValue_sub_of_two_mul_le n k hn hk)
  rw [norm_div,← ofReal_sub,norm_real,Real.norm_eq_abs,abs_of_pos hpos]
  simp only [norm_natCast]

end NLS.KdV
