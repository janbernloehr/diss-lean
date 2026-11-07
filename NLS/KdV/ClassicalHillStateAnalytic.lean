import NLS.KdV.ClassicalHillFlow
import NLS.FunctionalAnalysis.ComplexVolterraAnalytic

/-! Whole-curve Banach analyticity of the ACTUAL scalar Hill state.
The potential enters as the literal lower-left coefficient; its physical
position/derivative normalization is preserved at every complex energy. -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.KdV

def classicalHillSourceCurveCLM :
    Curve ℂ →L[ℂ] Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1)
    (ContinuousLinearMap.toSpanSingleton ℂ
      ((0 : (ℂ × ℂ) →L[ℂ] ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)))

theorem classicalHillSourceCurveCLM_apply (h : Curve ℂ) (t : Icc (0:ℝ) 1) (v : ℂ × ℂ) :
    classicalHillSourceCurveCLM h t v = (0,h t*v.1) := by
  change (h t) • (0,v.1) = _
  simp

def classicalHillComplexCoefficientCurve (q : Curve ℂ) (μ : ℂ) :
    Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  ContinuousMap.const _ (classicalHillCoefficient 0 μ)+classicalHillSourceCurveCLM q

theorem classicalHillComplexCoefficientCurve_apply (q : Curve ℂ) (μ : ℂ)
    (t : Icc (0:ℝ) 1) (v : ℂ × ℂ) :
    classicalHillComplexCoefficientCurve q μ t v = (v.2,(q t-μ)*v.1) := by
  simp only [classicalHillComplexCoefficientCurve,ContinuousMap.add_apply,ContinuousMap.const_apply,
    add_apply,classicalHillCoefficient_apply,classicalHillSourceCurveCLM_apply]
  ext <;> dsimp <;> ring

theorem realCoefficient_classicalHillComplexCoefficientCurve (q : Curve ℂ) (μ : ℂ) :
    realCoefficient (classicalHillComplexCoefficientCurve q μ) = classicalHillCoefficientCurve q μ := by
  apply ContinuousMap.ext
  intro t
  apply ContinuousLinearMap.ext
  intro v
  change classicalHillComplexCoefficientCurve q μ t v = classicalHillCoefficient (q t) μ v
  rw [classicalHillComplexCoefficientCurve_apply,classicalHillCoefficient_apply]

def classicalHillStateCurve (q : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  solutionCurve (realCoefficient (classicalHillComplexCoefficientCurve q μ)) v

theorem classicalHillStateCurve_apply (q : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalHillStateCurve q μ v t = classicalHillFlow q μ v t := by
  rw [classicalHillStateCurve,realCoefficient_classicalHillComplexCoefficientCurve,← solution_coe]
  rfl

theorem hasFDerivAt_classicalHillComplexCoefficientCurve (q : Curve ℂ) (μ : ℂ) :
    HasFDerivAt (fun r => classicalHillComplexCoefficientCurve r μ) classicalHillSourceCurveCLM q := by
  have hL : HasFDerivAt classicalHillSourceCurveCLM classicalHillSourceCurveCLM q :=
    classicalHillSourceCurveCLM.hasFDerivAt
  change HasFDerivAt
    (fun r => ContinuousMap.const (Icc (0:ℝ) 1) (classicalHillCoefficient 0 μ)+classicalHillSourceCurveCLM r)
    classicalHillSourceCurveCLM q
  exact (hasFDerivAt_const_add_iff (𝕜 := ℂ)
    (ContinuousMap.const (Icc (0:ℝ) 1) (classicalHillCoefficient 0 μ))).mpr hL

theorem analyticOnNhd_classicalHillStateCurve_potential (μ : ℂ) (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun q => classicalHillStateCurve q μ v) univ := by
  intro q _
  have hL : AnalyticAt ℂ classicalHillSourceCurveCLM q :=
    _root_.ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := Curve ℂ)
      (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) classicalHillSourceCurveCLM q
  have hA : AnalyticAt ℂ (fun r => classicalHillComplexCoefficientCurve r μ) q :=
    analyticAt_const.add hL
  exact ((analyticOnNhd_solutionCurve_coefficient v)
    (classicalHillComplexCoefficientCurve q μ) (mem_univ _)).comp
      (f := fun r => classicalHillComplexCoefficientCurve r μ) hA

theorem analyticOnNhd_classicalHillFlow_potential (μ : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    AnalyticOnNhd ℂ (fun q => classicalHillFlow q μ v t) univ := by
  have he : (fun q => classicalHillFlow q μ v t) = fun q => classicalHillStateCurve q μ v t :=
    funext (fun q => (classicalHillStateCurve_apply q μ v t).symm)
  rw [he]
  intro q hq
  exact ((ContinuousMap.evalCLM ℂ t : Curve (ℂ × ℂ) →L[ℂ] ℂ × ℂ).analyticAt _).comp
    (analyticOnNhd_classicalHillStateCurve_potential μ v q hq)

end NLS.KdV
