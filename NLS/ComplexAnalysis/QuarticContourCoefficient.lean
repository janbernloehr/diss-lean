import NLS.ComplexAnalysis.QuadraticContourCoefficient
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Extracting physical energy from a quartic primitive on energy circles -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_quartic_circle_coefficient_sub_le
    (f : ℂ → ℂ) (A H : ℂ) (r C : ℝ) (hr : 0 < r)
    (hf : CircleIntegrable f 0 (r^2))
    (hbound : ∀ z ∈ sphere (0 : ℂ) (r^2), r^3*‖f z-z^2+A+H/(4*z)‖ ≤ C) :
    ‖(-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(0,r^2), f z)-H‖ ≤ 4*C/r := by
  have hR : 0 < r^2 := sq_pos_of_pos hr
  have hne (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (r^2)) : z ≠ 0 := by
    have hn : ‖z‖ = r^2 := by simpa only [mem_sphere_iff_norm,sub_zero] using hz
    exact norm_pos_iff.mp (hn.symm ▸ hR)
  have hInv : ContinuousOn (fun z : ℂ => z⁻¹) (sphere 0 (r^2)) := continuousOn_id.inv₀ hne
  have hpolefun : (fun z : ℂ => H/(4*z)) = (fun z => (H/4)*z⁻¹) := by
    funext z
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hpoleint : CircleIntegrable (fun z : ℂ => H/(4*z)) 0 (r^2) := by
    rw [hpolefun]
    exact (continuousOn_const.mul hInv).circleIntegrable hR.le
  have hpoly : Differentiable ℂ (fun z : ℂ => z^2-A) := by fun_prop
  have hpolyint : CircleIntegrable (fun z : ℂ => z^2-A) 0 (r^2) :=
    hpoly.continuous.continuousOn.circleIntegrable hR.le
  have hpolyzero : (∮ z in C(0,r^2), z^2-A) = 0 :=
    (DiffContOnCl.mk_ball hpoly.differentiableOn hpoly.continuous.continuousOn).circleIntegral_eq_zero hR.le
  have hpole : (∮ z in C(0,r^2), H/(4*z)) = (H/2)*((Real.pi : ℂ)*I) := by
    rw [hpolefun,circleIntegral.integral_const_mul]
    have hi : (∮ z in C(0,r^2), z⁻¹) = (2*Real.pi*I : ℂ) := by
      simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) hR.ne'
    rw [hi]
    ring
  have hfun : (fun z : ℂ => f z-z^2+A+H/(4*z)) = (fun z => (f z-(z^2-A))+H/(4*z)) := by
    funext z;ring
  have hint : (∮ z in C(0,r^2), f z-z^2+A+H/(4*z)) =
      (∮ z in C(0,r^2), f z)+(H/2)*((Real.pi : ℂ)*I) := by
    have hisub : CircleIntegrable (fun z => f z-(z^2-A)) 0 (r^2) := hf.sub hpolyint
    rw [hfun,circleIntegral.integral_add hisub hpoleint,
      circleIntegral.integral_sub hf hpolyint,hpolyzero,sub_zero,hpole]
  have he : (-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(0,r^2), f z-z^2+A+H/(4*z)) =
      (-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(0,r^2), f z)-H := by
    rw [hint,mul_add]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  have hb : ‖∮ z in C(0,r^2), f z-z^2+A+H/(4*z)‖ ≤ 2*Real.pi*r^2*(C/r^3) := by
    apply circleIntegral.norm_integral_le_of_norm_le_const hR.le
    intro z hz
    exact (le_div_iff₀ (pow_pos hr 3)).mpr (by simpa only [mul_comm] using hbound z hz)
  rw [←he,norm_mul]
  have hn : ‖(-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹‖ = 2/Real.pi := by
    rw [norm_mul,norm_neg,norm_ofNat,norm_inv,norm_mul,norm_mul,norm_ofNat,
      norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_I,mul_one]
    field_simp
    norm_num
  rw [hn]
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2/Real.pi)).trans_eq
  field_simp
  ring

end NLS.ComplexAnalysis
