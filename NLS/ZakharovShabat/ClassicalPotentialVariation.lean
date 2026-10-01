import NLS.FunctionalAnalysis.ComplexVolterraVariation
import NLS.ZakharovShabat.ClassicalChainOperator

/-! # Actual potential derivatives of the classical fundamental solutions

The derivative in an arbitrary continuous potential direction is the
zero-initial solution of the linearized Zakharov--Shabat equation.
This identifies the derivative of the entire solution curve, and gives
a C1 physical representative with the original off-diagonal signs.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalPotentialCoefficientCLM :
    Curve (ℂ × ℂ) →L[ℂ] Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  classicalCoefficientCurveCLM.comp (ContinuousLinearMap.inr ℂ ℂ (Curve (ℂ × ℂ)))

@[simp] theorem classicalPotentialCoefficientCLM_apply
    (H : Curve (ℂ × ℂ)) (t : Icc (0 : ℝ) 1) (u : ℂ × ℂ) :
    classicalPotentialCoefficientCLM H t u = (I*(H t).1*u.2,-I*(H t).2*u.1) := by
  change classicalODECoefficient (H t) 0 u = _
  simp [classicalODECoefficient_apply]

def classicalPotentialVariationSource (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Curve (ℂ × ℂ) :=
  coefficientVariationSource (classicalPotentialCoefficientCLM H) (classicalSolutionCurve Φ z v)

@[simp] theorem classicalPotentialVariationSource_apply
    (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalPotentialVariationSource Φ H z v t =
      (I*(H t).1*(classicalSolution Φ z v t).2,
        -I*(H t).2*(classicalSolution Φ z v t).1) := by
  simp [classicalPotentialVariationSource,coefficientVariationSource]

def classicalPotentialVariationCurve (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Curve (ℂ × ℂ) :=
  forcedSolutionCurve (classicalCoefficientCurveCLM (z,Φ)) (classicalPotentialVariationSource Φ H z v) 0

theorem fderiv_classicalSolutionCurve_potential
    (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    (fderiv ℂ (fun Ψ => classicalSolutionCurve Ψ z v) Φ) H =
      classicalPotentialVariationCurve Φ H z v := by
  let A := classicalCoefficientCurveCLM (z,Φ)
  let u : Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) → Curve (ℂ × ℂ) :=
    fun C => solutionCurve (realCoefficient C) v
  have hA : HasFDerivAt (fun Ψ : Curve (ℂ × ℂ) => classicalCoefficientCurveCLM (z,Ψ))
      classicalPotentialCoefficientCLM Φ := by
    have hc : HasFDerivAt classicalCoefficientCurveCLM classicalCoefficientCurveCLM (z,Φ) :=
      classicalCoefficientCurveCLM.hasFDerivAt
    have hi : HasFDerivAt (fun Ψ : Curve (ℂ × ℂ) => (z,Ψ))
        (ContinuousLinearMap.inr ℂ ℂ (Curve (ℂ × ℂ))) Φ :=
      hasFDerivAt_prodMk_right z Φ
    convert! HasFDerivAt.comp (𝕜 := ℂ) (E := Curve (ℂ × ℂ))
      (F := ℂ × Curve (ℂ × ℂ)) (G := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) Φ hc hi using 1
  have hu : HasFDerivAt u (fderiv ℂ u A) A :=
    ((analyticOnNhd_solutionCurve_coefficient v) A (mem_univ _)).differentiableAt.hasFDerivAt
  have heq : (fun Ψ => classicalSolutionCurve Ψ z v) =
      (fun Ψ : Curve (ℂ × ℂ) => u (classicalCoefficientCurveCLM (z,Ψ))) := by
    funext Ψ
    unfold classicalSolutionCurve u
    rw [realCoefficient_classicalCoefficientCurve]
  have hfd := (HasFDerivAt.comp (𝕜 := ℂ) (E := Curve (ℂ × ℂ))
    (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) (G := Curve (ℂ × ℂ)) Φ hu hA).fderiv
  change fderiv ℂ (fun Ψ => u (classicalCoefficientCurveCLM (z,Ψ))) Φ = _ at hfd
  rw [← heq] at hfd
  rw [hfd,ContinuousLinearMap.comp_apply]
  change (fderiv ℂ (fun C => solutionCurve (realCoefficient C) v) A)
    (classicalPotentialCoefficientCLM H) = _
  rw [fderiv_solutionCurve_coefficient_eq_forced]
  have hbase : solutionCurve (realCoefficient A) v = classicalSolutionCurve Φ z v := by
    unfold A classicalSolutionCurve
    rw [realCoefficient_classicalCoefficientCurve]
  rw [hbase]
  rfl

def classicalPotentialVariation (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) : ℝ → ℂ × ℂ :=
  forcedSolution (classicalCoefficientCurveCLM (z,Φ)) (classicalPotentialVariationSource Φ H z v) 0

theorem classicalPotentialVariation_coe (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    classicalPotentialVariation Φ H z v t = classicalPotentialVariationCurve Φ H z v t :=
  forcedSolution_coe _ _ _ t

@[simp] theorem classicalPotentialVariation_zero (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    classicalPotentialVariation Φ H z v 0 = 0 := forcedSolution_zero _ _ _

theorem contDiff_classicalPotentialVariation (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    ContDiff ℝ 1 (classicalPotentialVariation Φ H z v) := contDiff_forcedSolution _ _ _

theorem hasDerivAt_classicalPotentialVariation (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalPotentialVariation Φ H z v)
      (classicalODECoefficient (Φ t) z (classicalPotentialVariation Φ H z v t)+
        (I*(H t).1*(classicalSolution Φ z v t).2,
          -I*(H t).2*(classicalSolution Φ z v t).1)) t := by
  simpa only [classicalCoefficientCurveCLM_apply,classicalPotentialVariationSource_apply] using!
    hasDerivAt_forcedSolution_coe (classicalCoefficientCurveCLM (z,Φ))
      (classicalPotentialVariationSource Φ H z v) 0 t

/-- Analyticity holds in the supremum norm of the entire solution
curve, so evaluating its potential derivative at the endpoint is valid. -/
theorem analyticOnNhd_classicalSolutionCurve_potential (z : ℂ) (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSolutionCurve Ψ z v) univ := by
  simp_rw [classicalSolutionCurve_eq_inverse]
  intro Φ _
  have hc := (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) classicalCoefficientCurveCLM (z,Φ)).comp
    (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)
  have hi := (analyticOnNhd_solutionOperator (classicalCoefficientCurveCLM (z,Φ)) (mem_univ _)).comp
    (f := fun Ψ : Curve (ℂ × ℂ) => classicalCoefficientCurveCLM (z,Ψ)) hc
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (ContinuousLinearMap.apply ℂ (Curve (ℂ × ℂ)) (ContinuousMap.const _ v)) _).comp hi

theorem fderiv_classicalSolution_potential (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSolution Ψ z v t) Φ) H =
      classicalPotentialVariation Φ H z v t := by
  have hf := ((analyticOnNhd_classicalSolutionCurve_potential z v) Φ (mem_univ _)).differentiableAt.hasFDerivAt
  let ev : Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := ContinuousMap.evalCLM ℂ t
  have he : HasFDerivAt ev ev (classicalSolutionCurve Φ z v) := ev.hasFDerivAt
  have hc := HasFDerivAt.comp (𝕜 := ℂ) (E := Curve (ℂ × ℂ)) (F := Curve (ℂ × ℂ))
    (G := ℂ × ℂ) Φ he hf
  have heq : (fun Ψ : Curve (ℂ × ℂ) => classicalSolutionCurve Ψ z v t) =
      (fun Ψ => classicalSolution Ψ z v t) := funext fun Ψ => classicalSolutionCurve_apply Ψ z v t
  have hfd := hc.fderiv
  change fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSolutionCurve Ψ z v t) Φ = _ at hfd
  rw [heq] at hfd
  rw [hfd,ContinuousLinearMap.comp_apply,fderiv_classicalSolutionCurve_potential]
  exact (classicalPotentialVariation_coe Φ H z v t).symm

end NLS.ZakharovShabat
