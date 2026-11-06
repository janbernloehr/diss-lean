import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

/-! # The physical quartic contour coefficient from a squared-phase remainder

A uniform fifth-order squared-phase remainder gives a uniform third-order
quartic remainder. The normalized circle integral then extracts the exact
coefficient -B/4 with an explicit inverse-frequency error. Integrability is
retained as a separate mathematical hypothesis for the contour algebra.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_raw_quartic_circle_coefficient_sub_le (f : ℂ → ℂ) (A B : ℂ) (r C : ℝ)
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
