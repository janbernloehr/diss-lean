import NLS.ComplexAnalysis.QuadraticContourCoefficient

/-! # Extracting the energy coefficient with its physical normalization -/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_energy_circle_coefficient_sub_le (f : ℂ → ℂ) (A B : ℂ) (r C : ℝ)
    (hr : 0 < r) (hf : CircleIntegrable (fun z => z*f z) 0 (r^2))
    (hbound : ∀ z ∈ sphere (0 : ℂ) (r^2),
      r^5 * ‖f z+z-A/(2*z)-B/(8*z^2)‖ ≤ C) :
    ‖((Real.pi : ℂ)*I)⁻¹ * (∮ z in C((0 : ℂ), r^2), z*f z) - B/4‖ ≤ 2*C/r := by
  let g : ℂ → ℂ := fun z => z*f z+z^2-A/2-z
  have hR : 0 < r^2 := sq_pos_of_pos hr
  have hi : CircleIntegrable (fun z : ℂ => z) 0 (r^2) := circleIntegrable_id _ _
  have hi2 : CircleIntegrable (fun z : ℂ => z^2) 0 (r^2) :=
    (continuousOn_id.pow 2).circleIntegrable hR.le
  have hc : CircleIntegrable (fun _ : ℂ => A/2) 0 (r^2) :=
    continuousOn_const.circleIntegrable hR.le
  have hsum : CircleIntegrable (fun z => z*f z+z^2) 0 (r^2) := hf.add hi2
  have hsub : CircleIntegrable (fun z => z*f z+z^2-A/2) 0 (r^2) := hsum.sub hc
  have hg : CircleIntegrable g 0 (r^2) := hsub.sub hi
  have hid : (∮ z in C((0 : ℂ), r^2), z) = 0 := by
    simpa only [sub_zero, zpow_one] using circleIntegral.integral_sub_zpow_of_ne
      (by decide : (1 : ℤ) ≠ -1) (0 : ℂ) (0 : ℂ) (r^2)
  have hi2d : (∮ z in C((0 : ℂ), r^2), z^2) = 0 := by
    simpa only [sub_zero, zpow_ofNat] using circleIntegral.integral_sub_zpow_of_ne
      (by decide : (2 : ℤ) ≠ -1) (0 : ℂ) (0 : ℂ) (r^2)
  have hc0 : (∮ z in C((0 : ℂ), r^2), A/2) = 0 := by
    have hzero : (∮ z in C((0 : ℂ), r^2), (1 : ℂ)) = 0 := by
      simpa only [sub_zero, zpow_zero] using circleIntegral.integral_sub_zpow_of_ne
        (by decide : (0 : ℤ) ≠ -1) (0 : ℂ) (0 : ℂ) (r^2)
    have hm : (∮ z in C((0 : ℂ), r^2), A/2) = (A/2)*(∮ z in C((0 : ℂ), r^2), (1 : ℂ)) := by
      simpa only [mul_one] using
        circleIntegral.integral_const_mul (A/2) (fun _ : ℂ => 1) (0 : ℂ) (r^2)
    rw [hzero, mul_zero] at hm
    exact hm
  have hgint : (∮ z in C((0 : ℂ), r^2), g z) = ∮ z in C((0 : ℂ), r^2), z*f z := by
    dsimp only [g]
    rw [circleIntegral.integral_sub hsub hi,
      circleIntegral.integral_sub hsum hc, circleIntegral.integral_add hf hi2,
      hi2d, hc0, hid]
    ring
  have hb (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (r^2)) :
      (r^2)^2 * ‖g z+z-(B/4)/(2*z)‖ ≤ C*r := by
    have hn : ‖z‖ = r^2 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
    have he : g z+z-(B/4)/(2*z) = z*(f z+z-A/(2*z)-B/(8*z^2)) := by
      dsimp only [g]
      field_simp
      ring
    rw [he, norm_mul, hn]
    calc
      _ = r*(r^5*‖f z+z-A/(2*z)-B/(8*z^2)‖) := by ring
      _ ≤ r*C := mul_le_mul_of_nonneg_left (hbound z hz) hr.le
      _ = C*r := mul_comm _ _
  have h := norm_quadratic_circle_coefficient_sub_le g (B/4) (r^2) (C*r) hR hg hb
  rw [hgint] at h
  apply h.trans_eq
  have hr0 := hr.ne'
  field_simp



end NLS.ComplexAnalysis
