import NLS.ComplexAnalysis.ParametricConvexPrimitive

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem real_affine_complex_integral_eq_intervalIntegral
    (f : ℂ → ℂ) (a θ : ℝ) :
    (∫ t in (0 : ℝ)..1, ((θ:ℂ)-(a:ℂ))*f ((a:ℂ)+(t:ℂ)*((θ:ℂ)-(a:ℂ)))) =
      ∫ x in a..θ, f (x : ℂ) := by
  have h := intervalIntegral.smul_integral_comp_mul_add (fun x : ℝ => f (x:ℂ))
    (a := (0:ℝ)) (b := 1) (θ-a) a
  have he : (fun t : ℝ => f (((θ-a)*t+a : ℝ) : ℂ)) =
      (fun t : ℝ => f ((a:ℂ)+(t:ℂ)*((θ:ℂ)-(a:ℂ)))) := by
    funext t
    congr 1
    push_cast
    ring
  rw [he] at h
  simp only [mul_zero,zero_add,mul_one,sub_add_cancel,Complex.real_smul] at h
  rw [intervalIntegral.integral_const_mul]
  simpa only [ofReal_sub] using h

end NLS.ComplexAnalysis
