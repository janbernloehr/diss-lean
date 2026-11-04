import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ComplexAnalysis



theorem continuous_circleIntegral_of_continuous_joint_on_sphere
    {A : Type*} [TopologicalSpace A] [FirstCountableTopology A] [LocallyCompactSpace A]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : A × ℂ → E) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hF : ContinuousOn F (univ ×ˢ sphere c R)) :
    Continuous (fun a : A => ∮ z in C(c,R), F (a,z)) := by
  have hmap : Continuous (fun p : A × ℝ => (p.1,circleMap c R p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hsection : Continuous (fun p : A × ℝ => F (p.1,circleMap c R p.2)) :=
    hF.comp_continuous hmap (fun p => ⟨mem_univ _,circleMap_mem_sphere c hR p.2⟩)
  have hderiv : Continuous (fun p : A × ℝ => deriv (circleMap c R) p.2) := by
    simp only [deriv_circleMap]
    fun_prop
  have hG : Continuous (fun p : A × ℝ =>
      deriv (circleMap c R) p.2 • F (p.1,circleMap c R p.2)) := hderiv.smul hsection
  have hi := continuous_parametric_integral_of_continuous (μ := MeasureTheory.volume)
    (f := fun a θ => deriv (circleMap c R) θ • F (a,circleMap c R θ))
    hG (s := Icc 0 (2*Real.pi)) isCompact_Icc
  simpa only [circleIntegral_def_Icc] using hi

end NLS.ComplexAnalysis
