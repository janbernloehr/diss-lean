import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

/-! # The physical quartic contour coefficient from a squared-phase remainder

A uniform fifth-order squared-phase remainder gives a uniform third-order
quartic remainder. The normalized circle integral then extracts the exact
coefficient -B/4 with an explicit inverse-frequency error. Integrability is
retained as a separate mathematical hypothesis for the contour algebra.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem scaled_square_shift_bound (v z A B : ℂ) (r C : ℝ)
    (hr : 1 ≤ r) (hz : ‖z‖ = r^2)
    (hbound : r^5*‖v+z-A/(2*z)-B/(8*z^2)‖ ≤ C) :
    r^2*‖v+z‖ ≤ ‖A‖/2+‖B‖/8+C := by
  have hrp : 0 < r := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hz.symm ▸ sq_pos_of_pos hrp)
  have he : v+z = (v+z-A/(2*z)-B/(8*z^2))+A/(2*z)+B/(8*z^2) := by ring
  have hb : ‖(v+z-A/(2*z)-B/(8*z^2))+A/(2*z)+B/(8*z^2)‖ ≤
      ‖v+z-A/(2*z)-B/(8*z^2)‖+‖A/(2*z)‖+‖B/(8*z^2)‖ := norm_add₃_le
  rw [← he,norm_div,norm_div,norm_mul,norm_mul,norm_pow,hz] at hb
  norm_num only [Complex.norm_ofNat] at hb
  have hr2 : 1 ≤ r^2 := one_le_pow₀ hr
  have hr3 : 1 ≤ r^3 := one_le_pow₀ hr
  have hr25 : r^2 ≤ r^5 := by
    calc
      r^2 ≤ r^2*r^3 := le_mul_of_one_le_right (sq_nonneg r) hr3
      _ = r^5 := by ring
  have heB : r^2*(‖B‖/(8*(r^2)^2)) ≤ ‖B‖/8 := by
    have h : ‖B‖/(8*r^2) ≤ ‖B‖/8 :=
      div_le_div_of_nonneg_left (norm_nonneg B) (by norm_num) (by nlinarith)
    apply le_trans (le_of_eq ?_) h
    field_simp
  have heA : r^2*(‖A‖/(2*r^2)) = ‖A‖/2 := by field_simp
  have heE : r^2*‖v+z-A/(2*z)-B/(8*z^2)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hr25 (norm_nonneg _)).trans hbound
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg r)
  rw [mul_add,mul_add,heA] at hb'
  linarith

theorem quartic_remainder_of_square_remainder (v z A B : ℂ) (r C D : ℝ)
    (hr : 1 ≤ r) (hD : 0 ≤ D) (hz : ‖z‖ = r^2)
    (hbound : r^5*‖v+z-A/(2*z)-B/(8*z^2)‖ ≤ C)
    (hshift : r^2*‖v+z‖ ≤ D) :
    r^3*‖v^2-z^2+A+B/(4*z)‖ ≤ 2*C+D^2 := by
  have hrp : 0 < r := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hz.symm ▸ sq_pos_of_pos hrp)
  have he : v^2-z^2+A+B/(4*z) =
      -2*z*(v+z-A/(2*z)-B/(8*z^2))+(v+z)^2 := by field_simp;ring
  have hb := norm_add_le (-2*z*(v+z-A/(2*z)-B/(8*z^2))) ((v+z)^2)
  rw [← he,norm_mul,norm_mul,norm_neg,norm_ofNat,hz,norm_pow] at hb
  have hsq : (r^2*‖v+z‖)^2 ≤ D^2 := sq_le_sq₀ (by positivity) hD |>.mpr hshift
  have hr34 : r^3 ≤ r^4 := by nlinarith [pow_pos hrp 3]
  have hlast : r^3*‖v+z‖^2 ≤ D^2 := by
    apply (mul_le_mul_of_nonneg_right hr34 (sq_nonneg _)).trans
    simpa only [mul_pow,← pow_mul,Nat.reduceMul] using hsq
  have hb' := mul_le_mul_of_nonneg_left hb (pow_nonneg hrp.le 3)
  have hew : r^3*(2*r^2*‖v+z-A/(2*z)-B/(8*z^2)‖+‖v+z‖^2) =
      2*(r^5*‖v+z-A/(2*z)-B/(8*z^2)‖)+r^3*‖v+z‖^2 := by ring
  rw [hew] at hb'
  linarith

theorem norm_quartic_circle_coefficient_sub_le (f : ℂ → ℂ) (A B : ℂ) (r C : ℝ)
    (hr : 0 < r) (hf : CircleIntegrable f 0 (r^2))
    (hbound : ∀ z ∈ sphere (0 : ℂ) (r^2), r^3*‖f z-z^2+A+B/(4*z)‖ ≤ C) :
    ‖(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(0,r^2), f z)+B/4‖ ≤ C/r := by
  have hR : 0 < r^2 := sq_pos_of_pos hr
  have hne (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (r^2)) : z ≠ 0 := by
    have hn : ‖z‖ = r^2 := by simpa only [mem_sphere_iff_norm,sub_zero] using hz
    exact norm_pos_iff.mp (hn.symm ▸ hR)
  have hi2 : CircleIntegrable (fun z : ℂ => z^2) 0 (r^2) :=
    (continuousOn_id.pow 2).circleIntegrable hR.le
  have hiA : CircleIntegrable (fun _ : ℂ => A) 0 (r^2) := circleIntegrable_const _ _ _
  have hiB : CircleIntegrable (fun z : ℂ => B/(4*z)) 0 (r^2) :=
    (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun z hz => mul_ne_zero (by norm_num) (hne z hz))).circleIntegrable hR.le
  have hi2zero : (∮ z in C((0 : ℂ),r^2), z^2) = 0 := by
    simpa only [sub_zero,zpow_ofNat] using circleIntegral.integral_sub_zpow_of_ne
      (by decide : (2 : ℤ) ≠ -1) (0 : ℂ) (0 : ℂ) (r^2)
  have hiAzero : (∮ z in C((0 : ℂ),r^2), A) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le (f := fun z : ℂ => A*z)
      (fun z _ => by simpa only [mul_one,id_eq] using! ((hasDerivAt_id z).const_mul A).hasDerivWithinAt)
  have hiBval : (∮ z in C((0 : ℂ),r^2), B/(4*z)) = (B/4)*(2*Real.pi*I) := by
    have he : (fun z : ℂ => B/(4*z)) = (fun z => (B/4)*z⁻¹) := by funext z; simp only [div_eq_mul_inv,mul_inv_rev];ring
    rw [he,circleIntegral.integral_const_mul]
    congr 1
    simpa only [sub_zero] using circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hR : (0 : ℂ) ∈ ball 0 (r^2))
  have hiSub : CircleIntegrable (fun z : ℂ => f z-z^2) 0 (r^2) := hf.sub hi2
  have hiAdd : CircleIntegrable (fun z : ℂ => f z-z^2+A) 0 (r^2) := hiSub.add hiA
  have hi : (∮ z in C((0 : ℂ),r^2), f z-z^2+A+B/(4*z)) =
      (∮ z in C((0 : ℂ),r^2), f z)+(B/4)*(2*Real.pi*I) := by
    rw [circleIntegral.integral_add hiAdd hiB,
      circleIntegral.integral_add hiSub hiA,circleIntegral.integral_sub hf hi2,
      hi2zero,hiAzero,hiBval,sub_zero,add_zero]
  have he : (2*Real.pi*I : ℂ)⁻¹*(∮ z in C((0 : ℂ),r^2), f z-z^2+A+B/(4*z)) =
      (2*Real.pi*I : ℂ)⁻¹*(∮ z in C((0 : ℂ),r^2), f z)+B/4 := by
    rw [hi,mul_add]
    have hp : (2*Real.pi*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
  rw [← he]
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (f := fun z => f z-z^2+A+B/(4*z)) (C := C/r^3) (fun z hz =>
      (le_div_iff₀ (pow_pos hr 3)).mpr (by simpa only [mul_comm] using hbound z hz))
  apply (show ‖(2*Real.pi*I : ℂ)⁻¹*(∮ z in C((0 : ℂ),r^2), f z-z^2+A+B/(4*z))‖ ≤ r^2*(C/r^3) from hb).trans_eq
  field_simp

end NLS.ComplexAnalysis
