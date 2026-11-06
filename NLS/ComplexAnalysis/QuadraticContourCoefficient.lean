import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

/-! # Extracting a quadratic trace coefficient from a uniform circle remainder

The normalization (pi*i)^(-1) reads A from the coefficient A/(2*z).
A second-order weighted circle remainder gives an explicit error 2*C/R.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_quadratic_circle_coefficient_sub_le (f : ℂ → ℂ) (A : ℂ) (R C : ℝ)
    (hR : 0 < R) (hf : CircleIntegrable f 0 R)
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, R^2 * ‖f z+z-A/(2*z)‖ ≤ C) :
    ‖((Real.pi : ℂ)*I)⁻¹ * (∮ z in C((0 : ℂ), R), f z) - A‖ ≤ 2*C/R := by
  have hne (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ≠ 0 := by
    have hn : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    exact norm_pos_iff.mp (hn.symm ▸ hR)
  have hInv : ContinuousOn (fun z : ℂ => z⁻¹) (sphere 0 R) := continuousOn_id.inv₀ hne
  have hpolefun : (fun z : ℂ => A/(2*z)) = (fun z => (A/2)*z⁻¹) := by
    funext z
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hpoleint : CircleIntegrable (fun z : ℂ => A/(2*z)) 0 R := by
    rw [hpolefun]
    exact (continuousOn_const.mul hInv).circleIntegrable hR.le
  have hid : (∮ z in C((0 : ℂ), R), z) = 0 := by
    simpa only [sub_zero, zpow_one] using
      circleIntegral.integral_sub_zpow_of_ne (by decide : (1 : ℤ) ≠ -1) (0 : ℂ) (0 : ℂ) R
  have hpole : (∮ z in C((0 : ℂ), R), A/(2*z)) = A*((Real.pi : ℂ)*I) := by
    rw [hpolefun, circleIntegral.integral_const_mul]
    have hinv : (∮ z in C((0 : ℂ), R), z⁻¹) = 2*Real.pi*I := by
      simpa only [sub_zero] using circleIntegral.integral_sub_inv_of_mem_ball
        (mem_ball_self hR : (0 : ℂ) ∈ ball 0 R)
    rw [hinv]
    ring
  have hiadd : CircleIntegrable (fun z : ℂ => f z+z) 0 R := hf.add (circleIntegrable_id 0 R)
  have hint : (∮ z in C((0 : ℂ), R), f z+z-A/(2*z)) =
      (∮ z in C((0 : ℂ), R), f z) - A*((Real.pi : ℂ)*I) := by
    rw [circleIntegral.integral_sub hiadd hpoleint,
      circleIntegral.integral_add hf (circleIntegrable_id 0 R), hid, add_zero, hpole]
  have he : ((Real.pi : ℂ)*I)⁻¹ * (∮ z in C((0 : ℂ), R), f z+z-A/(2*z)) =
      ((Real.pi : ℂ)*I)⁻¹ * (∮ z in C((0 : ℂ), R), f z) - A := by
    rw [hint, mul_sub]
    have hn : (Real.pi : ℂ)*I ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
  have hb : ‖∮ z in C((0 : ℂ), R), f z+z-A/(2*z)‖ ≤ 2*Real.pi*R*(C/R^2) := by
    apply circleIntegral.norm_integral_le_of_norm_le_const hR.le
    intro z hz
    exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by simpa only [mul_comm] using hbound z hz)
  rw [← he, norm_mul]
  have hn : ‖((Real.pi : ℂ)*I)⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
  rw [hn]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr Real.pi_pos.le)).trans_eq
  field_simp

end NLS.ComplexAnalysis
