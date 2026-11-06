import NLS.ComplexAnalysis.ParametricCircleIntegral

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem circleIntegral_source_fderiv_eq_zero
    (F : ℂ × A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hF : AnalyticOnNhd ℂ F D) (c : ℂ) (r : ℝ) (hr : 0≤r) (p h : A)
    (hc : ∀ z∈sphere c r, (z,p)∈D)
    (hzero : ∀ z∈sphere c r, (fderiv ℂ (fun b : A => F (z,b)) p) h=0) :
    DifferentiableAt ℂ (fun b : A => ∮ z in C(c,r),F (z,b)) p ∧
      (fderiv ℂ (fun b : A => ∮ z in C(c,r),F (z,b)) p) h=0 := by
  obtain ⟨V,hV,hpV,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F D hD hF c r p hc
  have hdom (b : A) (hb : b∈V) (θ : ℝ) : (circleMap c r θ,b)∈D :=
    (hbound _ (circleMap_mem_sphere c hr θ) b hb).1
  have hbd (b : A) (hb : b∈V) (θ : ℝ) : ‖fderiv ℂ F (circleMap c r θ,b)‖≤M :=
    (hbound _ (circleMap_mem_sphere c hr θ) b hb).2
  refine ⟨differentiableAt_circleIntegral_of_jointAnalytic F D hD hF c r hr V hV p hpV M hdom hbd,?_⟩
  rw [fderiv_circleIntegral_apply_of_jointAnalytic F D hD hF c r hr V hV p hpV M hdom hbd h]
  calc
    _ = ∮ z in C(c,r),(0 : ℂ) := by
      apply circleIntegral.integral_congr hr
      exact hzero
    _ = 0 := by simp only [circleIntegral,smul_zero,intervalIntegral.integral_zero]

end NLS.ComplexAnalysis
