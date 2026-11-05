import NLS.ComplexAnalysis.EndpointRootBounds
import NLS.ComplexAnalysis.AnalyticTwoZeroRoot

/-! # Nonvanishing standard roots, quotient perturbations and a gap-distance bound for critical endpoint ratios. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat
namespace NLS.ComplexAnalysis
theorem endpointRoot_ne_zero_of_not_mem_segment (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    endpointRoot a b z ≠ 0 := by
  intro he
  have hs := endpointRoot_sq a b z hz
  rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  rcases mul_eq_zero.mp hs.symm with ha | hb
  · exact hz ((sub_eq_zero.mp ha) ▸ left_mem_segment ℝ a b)
  · exact hz ((sub_eq_zero.mp hb) ▸ right_mem_segment ℝ a b)


theorem norm_div_sub_one_le_of_half_error (a b : ℂ) (A B : ℝ)
    (ha : ‖a-1‖ ≤ A) (hb : ‖b-1‖ ≤ B) (hB : B ≤ 1/2) :
    ‖a/b-1‖ ≤ 2*(A+B) := by
  have hrev := norm_sub_norm_le (1 : ℂ) b
  rw [norm_one,norm_sub_rev (1 : ℂ) b] at hrev
  have hlo : 1/2 ≤ ‖b‖ := by linarith
  have hbpos : 0 < ‖b‖ := by linarith
  have hne : b ≠ 0 := norm_pos_iff.mp hbpos
  have hnum : ‖a-b‖ ≤ A+B := by
    rw [show a-b = (a-1)-(b-1) by ring]
    exact (norm_sub_le _ _).trans (add_le_add ha hb)
  have hsum : 0 ≤ A+B := (norm_nonneg (a-b)).trans hnum
  rw [div_sub_one hne,norm_div]
  calc
    _ ≤ (A+B)/‖b‖ := div_le_div_of_nonneg_right hnum hbpos.le
    _ ≤ (A+B)/(1/2) := div_le_div_of_nonneg_left hsum (by norm_num) hlo
    _ = _ := by ring


theorem norm_critical_endpoint_ratio_le (a b c : ℝ) (hab : a ≤ b) (hc : c ∈ Icc a b)
    (z : ℂ) (hd : (b-a)/2 < ‖(((a+b)/2 : ℝ) : ℂ)-z‖) :
    ‖((c : ℂ)-z)/endpointRoot a b z‖ ≤ 1+(b-a)/(‖(((a+b)/2 : ℝ) : ℂ)-z‖-(b-a)/2) := by
  let t := (a+b)/2
  let h := (b-a)/2
  let d := ‖(t : ℂ)-z‖
  have hh : 0 ≤ h := by dsimp only [h]; linarith
  have hdh : 0 < d-h := by exact sub_pos.mpr hd
  have hdpos : 0 < d := lt_of_le_of_lt hh hd
  have ht : (t : ℂ) ≠ z := sub_ne_zero.mp (norm_pos_iff.mp hdpos)
  have hr := norm_normalizedStandardRoot_sub_center_le (t : ℂ) (((b-a : ℝ) : ℂ)^2) z ht
  have he : normalizedStandardRoot (t : ℂ) (((b-a : ℝ) : ℂ)^2) z = endpointRoot a b z := by
    simp only [endpointRoot,t,ofReal_div,ofReal_add,ofReal_sub,ofReal_ofNat]
  rw [he,norm_pow,norm_real,Real.norm_eq_abs,sq_abs] at hr
  have hfrac : (b-a)^2/(4*d) ≤ h := by
    apply (div_le_iff₀ (by positivity : 0 < 4*d)).mpr
    dsimp only [h] at hh hd ⊢
    nlinarith
  have hdev : ‖endpointRoot a b z-((t : ℂ)-z)‖ ≤ h := hr.trans hfrac
  have hrev := norm_sub_norm_le ((t : ℂ)-z) (endpointRoot a b z)
  rw [norm_sub_rev ((t : ℂ)-z) (endpointRoot a b z)] at hrev
  have hroot : d-h ≤ ‖endpointRoot a b z‖ := by dsimp only [d]; linarith
  have hrootpos : 0 < ‖endpointRoot a b z‖ := hdh.trans_le hroot
  have hcmid : |c-t| ≤ h := by
    rw [abs_le]
    dsimp only [t,h]
    constructor <;> linarith [hc.1,hc.2]
  have hnum : ‖(c : ℂ)-z‖ ≤ d+h := by
    rw [show (c : ℂ)-z = ((c-t : ℝ) : ℂ)+((t : ℂ)-z) by push_cast; ring]
    apply (norm_add_le _ _).trans
    rw [norm_real,Real.norm_eq_abs]
    dsimp only [d]
    linarith
  rw [norm_div]
  calc
    _ ≤ (d+h)/‖endpointRoot a b z‖ := div_le_div_of_nonneg_right hnum hrootpos.le
    _ ≤ (d+h)/(d-h) := div_le_div_of_nonneg_left (by positivity) hdh hroot
    _ = _ := by
      change (d+h)/(d-h) = 1+(b-a)/(d-h)
      field_simp
      dsimp only [h]
      ring

end NLS.ComplexAnalysis
