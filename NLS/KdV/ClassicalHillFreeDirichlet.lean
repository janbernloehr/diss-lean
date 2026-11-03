import NLS.KdV.ClassicalHillDirichlet

/-! # The exact free normalized scalar Hill state

The two actual IVP formulas are reused from the shared KdV estimates
branch. The import uses the existing Dirichlet normalization to avoid
introducing duplicate frequency-characteristic declarations.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalHillFlow_free_sine (z : ℂ) (hz : z≠0) (t : Icc (0 : ℝ) 1) :
    classicalHillFlow 0 (z^2) (0,1) t=(sin (z*t.val)/z,cos (z*t.val)) := by
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve 0 (z^2)) (0,1)
    (fun x : ℝ => (sin (z*x)/z,cos (z*x))) (by fun_prop) (by simp) _ t.property
  intro s _
  have harg : HasDerivAt (fun w : ℂ => z*w) z (s.val : ℂ) := by
    convert! (hasDerivAt_id (s.val : ℂ)).const_mul z using 1
    ring
  have hsin := (harg.csin.div_const z).comp_ofReal
  have hcos := harg.ccos.comp_ofReal
  have hh := hsin.prodMk hcos
  change HasDerivAt (fun x : ℝ => (sin (z*x)/z,cos (z*x)))
    (cos (z*s.val),(0-z^2)*(sin (z*s.val)/z)) s.val
  convert! hh using 1
  apply Prod.ext <;> dsimp <;> field_simp [hz]
  ring

theorem classicalHillFlow_free_zero (t : Icc (0 : ℝ) 1) :
    classicalHillFlow 0 0 (0,1) t=((t.val : ℂ),1) := by
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve 0 0) (0,1)
    (fun x : ℝ => ((x : ℂ),1)) (by fun_prop) (by simp) _ t.property
  intro s _
  simp only [classicalHillCoefficientCurve,ContinuousMap.coe_mk,ContinuousLinearMap.coe_restrictScalars',
    classicalHillCoefficient_apply,ContinuousMap.zero_apply,sub_self,zero_mul]
  convert! Complex.ofRealCLM.hasDerivAt.prodMk (hasDerivAt_const s.val (1 : ℂ)) using 1

end NLS.KdV
