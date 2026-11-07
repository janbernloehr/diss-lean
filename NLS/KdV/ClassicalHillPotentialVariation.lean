import NLS.KdV.ClassicalHillStateAnalytic
import NLS.FunctionalAnalysis.ComplexVolterraVariation
import NLS.KdV.HillL2DirichletTerminal

/-! The ACTUAL potential Fréchet variation of the scalar Hill IVP is
the zero-initial forced state with source (0,h*F). Whole-curve and
terminal derivatives retain the original physical initial normalization. -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.KdV

def classicalHillPotentialVariationSource (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  coefficientVariationSource (classicalHillSourceCurveCLM h) (classicalHillStateCurve q μ v)

theorem classicalHillPotentialVariationSource_apply (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    classicalHillPotentialVariationSource q h μ v t = (0,h t*(classicalHillFlow q μ v t).1) := by
  change classicalHillSourceCurveCLM h t (classicalHillStateCurve q μ v t) = _
  rw [classicalHillSourceCurveCLM_apply,classicalHillStateCurve_apply]

def classicalHillPotentialVariationCurve (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  forcedSolutionCurve (classicalHillComplexCoefficientCurve q μ)
    (classicalHillPotentialVariationSource q h μ v) 0

def classicalHillPotentialVariation (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) : ℝ → ℂ × ℂ :=
  forcedSolution (classicalHillComplexCoefficientCurve q μ)
    (classicalHillPotentialVariationSource q h μ v) 0

theorem classicalHillPotentialVariation_coe (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    classicalHillPotentialVariation q h μ v t = classicalHillPotentialVariationCurve q h μ v t :=
  forcedSolution_coe _ _ _ t

theorem contDiff_classicalHillPotentialVariation (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) :
    ContDiff ℝ 1 (classicalHillPotentialVariation q h μ v) := contDiff_forcedSolution _ _ _

theorem classicalHillPotentialVariation_zero (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) :
    classicalHillPotentialVariation q h μ v 0 = 0 := forcedSolution_zero _ _ _

theorem hasDerivAt_classicalHillPotentialVariation (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillPotentialVariation q h μ v)
      ((classicalHillPotentialVariation q h μ v t).2,
        (q t-μ)*(classicalHillPotentialVariation q h μ v t).1+h t*(classicalHillFlow q μ v t).1) t := by
  have hd := hasDerivAt_forcedSolution_coe (classicalHillComplexCoefficientCurve q μ)
    (classicalHillPotentialVariationSource q h μ v) 0 t
  simpa only [classicalHillPotentialVariation,classicalHillComplexCoefficientCurve_apply,
    classicalHillPotentialVariationSource_apply,Prod.mk_add_mk,add_zero] using hd

theorem fderiv_classicalHillStateCurve_potential (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) :
    (fderiv ℂ (fun r => classicalHillStateCurve r μ v) q) h =
      classicalHillPotentialVariationCurve q h μ v := by
  let A := classicalHillComplexCoefficientCurve q μ
  let u := fun C : Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) => solutionCurve (realCoefficient C) v
  have hu : HasFDerivAt u (fderiv ℂ u A) A :=
    ((analyticOnNhd_solutionCurve_coefficient v) A (mem_univ _)).differentiableAt.hasFDerivAt
  have hfd := (HasFDerivAt.comp (𝕜 := ℂ) (E := Curve ℂ)
    (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) (G := Curve (ℂ × ℂ))
    q hu (hasFDerivAt_classicalHillComplexCoefficientCurve q μ)).fderiv
  change fderiv ℂ (fun r => classicalHillStateCurve r μ v) q = _ at hfd
  rw [hfd,ContinuousLinearMap.comp_apply]
  change (fderiv ℂ (fun C => solutionCurve (realCoefficient C) v) A) (classicalHillSourceCurveCLM h) = _
  rw [fderiv_solutionCurve_coefficient_eq_forced]
  rfl

theorem fderiv_classicalHillFlow_potential (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    (fderiv ℂ (fun r => classicalHillFlow r μ v t) q) h = classicalHillPotentialVariation q h μ v t := by
  have he : (fun r => classicalHillFlow r μ v t) = fun r => classicalHillStateCurve r μ v t :=
    funext (fun r => (classicalHillStateCurve_apply r μ v t).symm)
  rw [he]
  have hd := (analyticOnNhd_classicalHillStateCurve_potential μ v q (mem_univ _)).differentiableAt.hasFDerivAt
  have hfd := ((ContinuousMap.evalCLM ℂ t : Curve (ℂ × ℂ) →L[ℂ] ℂ × ℂ).hasFDerivAt.comp q hd).fderiv
  change fderiv ℂ (fun r => classicalHillStateCurve r μ v t) q = _ at hfd
  rw [hfd,ContinuousLinearMap.comp_apply,fderiv_classicalHillStateCurve_potential]
  exact (classicalHillPotentialVariation_coe q h μ v t).symm

theorem fderiv_classicalHillDirichlet_potential (q h : Curve ℂ) (μ : ℂ) :
    (fderiv ℂ (fun r => classicalHillDirichlet r μ) q) h =
      (classicalHillPotentialVariation q h μ (0,1) 1).1 := by
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hd := (analyticOnNhd_classicalHillFlow_potential μ (0,1) t q (mem_univ _)).differentiableAt.hasFDerivAt
  have hfd := ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp q hd).fderiv
  change fderiv ℂ (fun r => (classicalHillFlow r μ (0,1) t).1) q = _ at hfd
  rw [show (fun r => classicalHillDirichlet r μ) = fun r => (classicalHillFlow r μ (0,1) t).1 from rfl,hfd]
  change ((fderiv ℂ (fun r => classicalHillFlow r μ (0,1) t) q) h).1 = _
  rw [fderiv_classicalHillFlow_potential]

theorem fderiv_classicalHillDirichletTerminal_potential (q h : Curve ℂ) (μ : ℂ) :
    (fderiv ℂ (fun r => classicalHillDirichletTerminal r μ) q) h =
      (classicalHillPotentialVariation q h μ (0,1) 1).2 := by
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hd := (analyticOnNhd_classicalHillFlow_potential μ (0,1) t q (mem_univ _)).differentiableAt.hasFDerivAt
  have hfd := ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp q hd).fderiv
  change fderiv ℂ (fun r => (classicalHillFlow r μ (0,1) t).2) q = _ at hfd
  rw [show (fun r => classicalHillDirichletTerminal r μ) = fun r => (classicalHillFlow r μ (0,1) t).2 from rfl,hfd]
  change ((fderiv ℂ (fun r => classicalHillFlow r μ (0,1) t) q) h).2 = _
  rw [fderiv_classicalHillFlow_potential]

end NLS.KdV
