import NLS.FunctionalAnalysis.UnitComplexCurvePrimitive
import NLS.ComplexAnalysis.BilinearCircleIntegral

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.FunctionalAnalysis



/-- A genuine continuous spatial derivative passes through the Banach
contour integral by its bounded primitive representation. -/
theorem circleIntegral_curve_spatial_derivative
    (f g : ℂ → Curve ℂ) (c : ℂ) (R : ℝ) (hR : 0≤R)
    (hf : ContinuousOn f (sphere c R)) (hg : ContinuousOn g (sphere c R))
    (hAC : ∀ z∈sphere c R, AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (f z)) 0 1)
    (hD : ∀ z∈sphere c R, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (f z)) (NLS.LinearVolterra.extend (g z) x) x) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (∮ z in C(c,R),f z)) 0 1 ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
        HasDerivAt (NLS.LinearVolterra.extend (∮ z in C(c,R),f z))
          (NLS.LinearVolterra.extend (∮ z in C(c,R),g z) x) x := by
  let F := ∮ z in C(c,R),f z
  let G := ∮ z in C(c,R),g z
  let C : Curve ℂ →L[ℂ] Curve ℂ :=
    (ContinuousLinearMap.const ℂ (Icc (0 : ℝ) 1) : ℂ →L[ℂ] Curve ℂ).comp
      (ContinuousMap.evalCLM ℂ ⟨0,by norm_num⟩)
  have hpoint (z : ℂ) (hz : z∈sphere c R) : f z=C (f z)+unitComplexCurvePrimitive (g z) :=
    curve_eq_constant_add_unitComplexCurvePrimitive (f z) (g z) (hAC z hz) (hD z hz)
  have hCf : CircleIntegrable (fun z => C (f z)) c R :=
    (C.continuous.comp_continuousOn hf).circleIntegrable hR
  have hPg : CircleIntegrable (fun z => unitComplexCurvePrimitive (g z)) c R :=
    (unitComplexCurvePrimitive.continuous.comp_continuousOn hg).circleIntegrable hR
  have he : F=C F+unitComplexCurvePrimitive G := by
    dsimp only [F,G]
    rw [map_circleIntegral C (hf.circleIntegrable hR),
      map_circleIntegral unitComplexCurvePrimitive (hg.circleIntegrable hR),
      ← circleIntegral.integral_add hCf hPg]
    exact circleIntegral.integral_congr hR hpoint
  have hext : NLS.LinearVolterra.extend F=fun x => F ⟨0,by norm_num⟩+
      NLS.LinearVolterra.extend (unitComplexCurvePrimitive G) x := by
    exact congrArg (fun f : Curve ℂ => NLS.LinearVolterra.extend f) he
  change AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend F) 0 1 ∧ _
  rw [hext]
  refine ⟨absolutelyContinuousOnInterval_const_add (absolutelyContinuousOnInterval_unitComplexCurvePrimitive G) _,?_⟩
  filter_upwards [ae_hasDerivAt_unitComplexCurvePrimitive G] with x hx
  exact hx.const_add _

end NLS.FunctionalAnalysis
