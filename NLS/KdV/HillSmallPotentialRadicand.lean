import NLS.KdV.HillL2SmallPotentialTrace
import NLS.KdV.HillCharacteristicZeros
import NLS.ComplexAnalysis.InverseSquareRootBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV



theorem hillL2Radicand_free_error_small (q : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H) (hsmall : 4*Real.exp H*‖q‖ ≤ ‖z‖) :
    ‖hillL2Radicand q (z^2)-hillL2Radicand 0 (z^2)‖ ≤
      48*(Real.exp H)^3*‖q‖/‖z‖ := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hfree : hillL2Discriminant 0 (z^2) = 2*cos z := by
    have h := hillL2Discriminant_free_error_small 0 z hz H hH (by simp)
    simpa only [norm_zero,mul_zero,zero_div,norm_le_zero_iff,sub_eq_zero] using h
  have hc : ‖2*cos z‖ ≤ 2*Real.exp H := by
    rw [norm_mul,norm_ofNat]
    exact mul_le_mul_of_nonneg_left
      ((norm_complex_cos_le_exp_im z).trans (Real.exp_le_exp.mpr hH)) (by norm_num)
  have herr := hillL2Discriminant_free_error_small q z hz H hH hsmall
  have he : 8*(Real.exp H)^2*‖q‖/‖z‖ ≤ 2*Real.exp H := by
    apply (div_le_iff₀ hnorm).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2*Real.exp H by positivity)]
  have hsum : ‖hillL2Discriminant q (z^2)+2*cos z‖ ≤ 6*Real.exp H := by
    have ht := norm_add_le (hillL2Discriminant q (z^2)-2*cos z) (2*(2*cos z))
    have heq : hillL2Discriminant q (z^2)-2*cos z+2*(2*cos z) = hillL2Discriminant q (z^2)+2*cos z := by ring
    rw [heq,norm_mul,norm_ofNat] at ht
    linarith
  have hfac : hillL2Radicand q (z^2)-hillL2Radicand 0 (z^2) =
      (hillL2Discriminant q (z^2)-2*cos z)*(hillL2Discriminant q (z^2)+2*cos z) := by
    rw [hillL2Radicand,hillL2Radicand,hfree]
    ring
  rw [hfac,norm_mul]
  apply (mul_le_mul herr hsum (norm_nonneg _) (by positivity)).trans_eq
  ring

theorem hillL2Radicand_ratio_free_bound (q : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (H d : ℝ) (hH : |z.im| ≤ H) (hd : 0 < d)
    (hfree : d ≤ ‖hillL2Radicand 0 (z^2)‖)
    (hsmall : 4*Real.exp H*‖q‖ ≤ ‖z‖) :
    ‖hillL2Radicand q (z^2)/hillL2Radicand 0 (z^2)-1‖ ≤
      48*(Real.exp H)^3*‖q‖/(‖z‖*d) := by
  have hne : hillL2Radicand 0 (z^2) ≠ 0 := norm_pos_iff.mp (hd.trans_le hfree)
  rw [div_sub_one hne,norm_div]
  have he := hillL2Radicand_free_error_small q z hz H hH hsmall
  apply (div_le_div₀ (by positivity) he hd hfree).trans_eq
  ring

theorem hillL2Radicand_ratio_free_slitPlane (q : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (H d : ℝ) (hH : |z.im| ≤ H) (hd : 0 < d)
    (hfree : d ≤ ‖hillL2Radicand 0 (z^2)‖)
    (hsmall : 4*Real.exp H*‖q‖ ≤ ‖z‖)
    (hratio : 48*(Real.exp H)^3*‖q‖/(‖z‖*d) ≤ 1/2) :
    hillL2Radicand q (z^2)/hillL2Radicand 0 (z^2) ∈ slitPlane :=
  mem_slitPlane_of_norm_sub_one_le_half _
    ((hillL2Radicand_ratio_free_bound q z hz H d hH hd hfree hsmall).trans hratio)

theorem norm_inv_sqrt_hillL2Radicand_ratio_free_sub_one_le (q : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (H d : ℝ) (hH : |z.im| ≤ H) (hd : 0 < d)
    (hfree : d ≤ ‖hillL2Radicand 0 (z^2)‖)
    (hsmall : 4*Real.exp H*‖q‖ ≤ ‖z‖)
    (hratio : 48*(Real.exp H)^3*‖q‖/(‖z‖*d) ≤ 1/2) :
    ‖(Complex.sqrt (hillL2Radicand q (z^2)/hillL2Radicand 0 (z^2)))⁻¹-1‖ ≤
      96*(Real.exp H)^3*‖q‖/(‖z‖*d) := by
  have h := hillL2Radicand_ratio_free_bound q z hz H d hH hd hfree hsmall
  apply (norm_inv_sqrt_sub_one_le _ (h.trans hratio)).trans
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring

end NLS.KdV
