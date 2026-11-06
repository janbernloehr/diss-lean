import NLS.FunctionalAnalysis.UnitComplexCurveIntegral
import NLS.ComplexAnalysis.BilinearCircleIntegral

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.FunctionalAnalysis



/-- The existing unit-interval curve integral with its complex-linear structure. -/
def unitComplexCurveIntegralCLM : Curve ℂ →L[ℂ] ℂ where
  toFun := unitComplexCurveIntegral
  map_add' := unitComplexCurveIntegral.map_add
  map_smul' := by
    intro c f
    change (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (c • f) x)=
      c*(∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend f x)
    simp only [NLS.LinearVolterra.extend,ContinuousMap.smul_apply,smul_eq_mul]
    exact intervalIntegral.integral_const_mul c _
  cont := unitComplexCurveIntegral.continuous

theorem unitComplexCurveIntegralCLM_apply (f : Curve ℂ) :
    unitComplexCurveIntegralCLM f=unitComplexCurveIntegral f := rfl

/-- Bounded complex bilinear multiplication followed by the physical unit integral. -/
def unitComplexCurvePairing : Curve ℂ →L[ℂ] Curve ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.compL ℂ (Curve ℂ) (Curve ℂ) ℂ unitComplexCurveIntegralCLM).comp
    (ContinuousLinearMap.mul ℂ (Curve ℂ))

theorem unitComplexCurvePairing_apply (f g : Curve ℂ) :
    unitComplexCurvePairing f g=unitComplexCurveIntegral (f*g) := rfl

end NLS.FunctionalAnalysis
