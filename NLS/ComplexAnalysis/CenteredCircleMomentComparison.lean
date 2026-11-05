import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

/-! # Centered first moments retain a quadratic contour-radius bound -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_normalized_centered_circleIntegral_le (h : ℂ → ℂ) (c : ℂ) {R B : ℝ}
    (hR : 0 ≤ R) (hb : ∀ z ∈ sphere c R, ‖h z‖ ≤ B) :
    ‖(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), (z-c)*h z)‖ ≤ R^2*B := by
  have hbound (z : ℂ) (hz : z ∈ sphere c R) : ‖(z-c)*h z‖ ≤ R*B := by
    rw [norm_mul,mem_sphere_iff_norm.mp hz]
    exact mul_le_mul_of_nonneg_left (hb z hz) hR
  rw [norm_mul,norm_inv,norm_mul,norm_mul,norm_ofNat,norm_I,mul_one,
    norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply (mul_le_mul_of_nonneg_left (circleIntegral.norm_integral_le_of_norm_le_const hR hbound)
    (by positivity : 0 ≤ (2*Real.pi)⁻¹)).trans_eq
  field_simp

theorem normalized_first_moment_sub_eq_centered (f g : ℂ → ℂ) (c : ℂ) {R : ℝ}
    (hR : 0 ≤ R) (hf : ContinuousOn f (sphere c R)) (hg : ContinuousOn g (sphere c R))
    (hzero : (2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), f z) =
      (2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), g z)) :
    (2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), z*f z)-
      (2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), z*g z) =
      (2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), (z-c)*(f z-g z)) := by
  have hzf := (continuousOn_id.mul hf).circleIntegrable hR
  have hzg := (continuousOn_id.mul hg).circleIntegrable hR
  have hcf : CircleIntegrable (fun z => c*f z) c R := (continuousOn_const.mul hf).circleIntegrable hR
  have hcg : CircleIntegrable (fun z => c*g z) c R := (continuousOn_const.mul hg).circleIntegrable hR
  have he : (∮ z in C(c,R), (z-c)*(f z-g z)) =
      (∮ z in C(c,R), z*f z)-c*(∮ z in C(c,R), f z)-
        ((∮ z in C(c,R), z*g z)-c*(∮ z in C(c,R), g z)) := by
    calc
      _ = ∮ z in C(c,R), (z*f z-c*f z)-(z*g z-c*g z) := by
        apply circleIntegral.integral_congr hR
        intro z hz
        ring
      _ = _ := by
        rw [circleIntegral.integral_sub (f := fun z => z*f z-c*f z) (g := fun z => z*g z-c*g z) (hzf.sub hcf) (hzg.sub hcg),
          circleIntegral.integral_sub (f := fun z => z*f z) (g := fun z => c*f z) hzf hcf,circleIntegral.integral_sub (f := fun z => z*g z) (g := fun z => c*g z) hzg hcg,
          circleIntegral.integral_const_mul,circleIntegral.integral_const_mul]
  rw [he]
  linear_combination c*hzero

theorem norm_normalized_first_moment_sub_le (f g : ℂ → ℂ) (c : ℂ) {R B : ℝ}
    (hR : 0 ≤ R) (hf : ContinuousOn f (sphere c R)) (hg : ContinuousOn g (sphere c R))
    (hzero : (2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), f z) =
      (2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), g z))
    (hb : ∀ z ∈ sphere c R, ‖f z-g z‖ ≤ B) :
    ‖(2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), z*f z)-
      (2*Real.pi*I : ℂ)⁻¹*(∮ z in C(c,R), z*g z)‖ ≤ R^2*B := by
  rw [normalized_first_moment_sub_eq_centered f g c hR hf hg hzero]
  exact norm_normalized_centered_circleIntegral_le (fun z => f z-g z) c hR hb

end NLS.ComplexAnalysis
