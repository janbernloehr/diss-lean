import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ComplexAnalysis.NormalizedSquareRootBounds

/-! # Quantitative normalized endpoint-root bounds from endpoint displacement. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.ComplexAnalysis
theorem norm_normalizedStandardRoot_sub_center_le (t g z : ℂ) (ht : t ≠ z) :
    ‖normalizedStandardRoot t g z-(t-z)‖ ≤ ‖g‖/(4*‖t-z‖) := by
  have hw : 0 < ‖t-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ht)
  have he : normalizedStandardRoot t g z-(t-z) =
      (t-z)*(Complex.sqrt (1-g/(4*(t-z)^2))-1) := by unfold normalizedStandardRoot; ring
  rw [he,norm_mul]
  calc
    _ ≤ ‖t-z‖*‖(1-g/(4*(t-z)^2))-1‖ :=
      mul_le_mul_of_nonneg_left (norm_sqrt_sub_one_le _) (norm_nonneg _)
    _ = _ := by
      rw [show (1-g/(4*(t-z)^2))-1 = -(g/(4*(t-z)^2)) by ring,
        norm_neg,norm_div,norm_mul,norm_pow]
      norm_num
      field_simp

theorem norm_endpointRoot_div_sub_one_le (a b c D : ℝ) (z : ℂ)
    (hc : 1 ≤ c) (ha : |a-c| ≤ D) (hb : |b-c| ≤ D)
    (hlarge : 2*(D+‖z‖) < c) :
    ‖endpointRoot a b z/(c : ℂ)-1‖ ≤ (D+‖z‖+2*D^2)/c := by
  let t : ℝ := (a+b)/2
  have ht : |t-c| ≤ D := by dsimp only [t]; rcases abs_le.mp ha with ⟨ha1,ha2⟩; rcases abs_le.mp hb with ⟨hb1,hb2⟩; exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hg : |b-a| ≤ 2*D := by
    rcases abs_le.mp ha with ⟨ha1,ha2⟩; rcases abs_le.mp hb with ⟨hb1,hb2⟩
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hcpos : 0 < c := by linarith
  have hdist : ‖((t : ℂ)-z)-(c : ℂ)‖ ≤ D+‖z‖ := by
    rw [show ((t : ℂ)-z)-(c : ℂ) = ((t-c : ℝ) : ℂ)-z by push_cast; ring]
    exact (norm_sub_le _ _).trans (add_le_add (by simpa only [norm_real,Real.norm_eq_abs] using ht) le_rfl)
  have hw : c/2 < ‖(t : ℂ)-z‖ := by
    have hh := norm_sub_norm_le (c : ℂ) ((t : ℂ)-z)
    rw [norm_sub_rev (c : ℂ) ((t : ℂ)-z),norm_real,Real.norm_eq_abs,abs_of_pos hcpos] at hh
    linarith
  have hwpos : 0 < ‖(t : ℂ)-z‖ := by linarith
  have htne : (t : ℂ) ≠ z := by intro he; rw [he,sub_self,norm_zero] at hwpos; linarith
  have hroot := norm_normalizedStandardRoot_sub_center_le (t : ℂ) (((b-a : ℝ) : ℂ)^2) z htne
  have he : endpointRoot (a : ℂ) (b : ℂ) z = normalizedStandardRoot (t : ℂ) (((b-a : ℝ) : ℂ)^2) z := by
    simp only [endpointRoot,t,ofReal_div,ofReal_add,ofReal_ofNat,ofReal_sub]
  rw [← he,norm_pow,norm_real,Real.norm_eq_abs,sq_abs] at hroot
  have hq : (b-a)^2 ≤ (2*D)^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (b-a)) hg 2
  have hdiv : (b-a)^2/(4*‖(t : ℂ)-z‖) ≤ 2*D^2/c := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*‖(t : ℂ)-z‖) hcpos).mpr
    nlinarith [mul_nonneg (sq_nonneg D) (show 0 ≤ 2*‖(t : ℂ)-z‖-c by linarith),
      mul_nonneg (show 0 ≤ (2*D)^2-(b-a)^2 by linarith) hcpos.le]
  have hnorm : ‖endpointRoot (a : ℂ) (b : ℂ) z-(c : ℂ)‖ ≤ D+‖z‖+2*D^2/c := by
    have hh := dist_triangle (endpointRoot (a : ℂ) (b : ℂ) z) ((t : ℂ)-z) (c : ℂ)
    simp only [dist_eq_norm] at hh
    linarith
  have hdiv2 : 2*D^2/c ≤ 2*D^2 := div_le_self (by positivity) hc
  rw [show endpointRoot (a : ℂ) (b : ℂ) z/(c : ℂ)-1 =
    (endpointRoot (a : ℂ) (b : ℂ) z-(c : ℂ))/(c : ℂ) by
      rw [sub_div,div_self (show (c : ℂ) ≠ 0 by exact_mod_cast hcpos.ne')]]
  rw [norm_div,norm_real,Real.norm_eq_abs,abs_of_pos hcpos]
  exact (div_le_div_of_nonneg_right hnorm hcpos.le).trans
    (div_le_div_of_nonneg_right (by linarith) hcpos.le)

end NLS.ComplexAnalysis
