import NLS.ComplexAnalysis.QuarticContourCoefficient

noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_scaled_quartic_circle_coefficient_sub_le
    (f : ℂ → ℂ) (A H : ℂ) (r C : ℝ) (hr : 0<r)
    (hf : CircleIntegrable f 0 (r^2))
    (hbound : ∀ z∈sphere (0 : ℂ) (r^2), r^3*‖f z-z^2+A+H/(4*z)‖≤C) :
    ‖(-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(0,r^2), f z)-H‖≤4*C/r := by
  have h := norm_quartic_circle_coefficient_sub_le f A H r C hr hf hbound
  have he : (-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(0,r^2), f z)-H=
      (-4 : ℂ)*((2*Real.pi*I : ℂ)⁻¹*(∮ z in C(0,r^2), f z)+H/4) := by ring
  calc
    _ = 4*‖(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(0,r^2), f z)+H/4‖ := by rw [he,norm_mul];norm_num
    _ ≤ 4*(C/r) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

end NLS.ComplexAnalysis
