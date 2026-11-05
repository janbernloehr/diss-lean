import NLS.FunctionalAnalysis.ClosedUnitCurveContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.FunctionalAnalysis



/-- The actual complex-linear subspace of continuous closed unit curves. -/
def closedUnitCurveSubmodule : Submodule ℂ (Curve ℂ) where
  carrier := {f | f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩}
  zero_mem' := rfl
  add_mem' := by
    intro f g hf hg
    change f ⟨0,by norm_num⟩+g ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩+g ⟨1,by norm_num⟩
    rw [hf,hg]
  smul_mem' := by
    intro c f hf
    change c*f ⟨0,by norm_num⟩=c*f ⟨1,by norm_num⟩
    rw [hf]

/-- Closed physical unit-curve periodization is a bounded complex-linear map. -/
def closedUnitCurvePeriodTwoCLM : closedUnitCurveSubmodule →L[ℂ] C(AddCircle (2 : ℝ),ℂ) where
  toFun := fun f => closedUnitCurvePeriodTwo f.val f.property
  map_add' := by
    intro f g
    ext x
    refine Quotient.inductionOn x ?_
    intro t
    rfl
  map_smul' := by
    intro c f
    ext x
    refine Quotient.inductionOn x ?_
    intro t
    rfl
  cont := continuous_closedUnitCurvePeriodTwo_family (fun f : closedUnitCurveSubmodule => f.val)
    (fun f => f.property) continuous_subtype_val

private def unitTimeCurve : Curve ℂ := ⟨fun t => (t.val : ℂ),Complex.continuous_ofReal.comp continuous_subtype_val⟩

private def closedCurveCorrection : Curve ℂ →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.id ℂ (Curve ℂ)-
    (((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1))-
      (ContinuousMap.evalCLM ℂ (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1)) : Curve ℂ →L[ℂ] ℂ).smulRight unitTimeCurve)

private theorem closedCurveCorrection_mem (f : Curve ℂ) : closedCurveCorrection f∈closedUnitCurveSubmodule := by
  change f ⟨0,by norm_num⟩-(f ⟨1,by norm_num⟩-f ⟨0,by norm_num⟩)*(0 : ℂ)=
    f ⟨1,by norm_num⟩-(f ⟨1,by norm_num⟩-f ⟨0,by norm_num⟩)*(1 : ℂ)
  ring

/-- Subtracting the linear endpoint jump gives a bounded projection onto closed unit curves. -/
def closedUnitCurveProjectionCLM : Curve ℂ →L[ℂ] closedUnitCurveSubmodule :=
  closedCurveCorrection.codRestrict closedUnitCurveSubmodule closedCurveCorrection_mem

/-- The projection fixes every actual closed physical curve. -/
theorem closedUnitCurveProjectionCLM_fixed (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    (closedUnitCurveProjectionCLM f).val=f := by
  ext t
  change f t-(f ⟨1,by norm_num⟩-f ⟨0,by norm_num⟩)*(t.val : ℂ)=f t
  rw [hf,sub_self,zero_mul,sub_zero]

end NLS.FunctionalAnalysis
