import NLS.ZakharovShabat.ClassicalEndpointPoisson

/-! # Spectral variation of actual classical endpoint functionals

Differentiation of the Volterra solution in its spectral parameter gives
the forced source (-i u₁, i u₂). The adjugate kernel then expresses the
endpoint derivative as an integral of the forward and dual solutions.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The forcing produced by one spectral derivative. -/
def classicalSpectralVariationSource (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  coefficientVariationSource (classicalCoefficientCurveCLM (1,0)) (classicalSolutionCurve Φ z v)

@[simp] theorem classicalSpectralVariationSource_apply
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSpectralVariationSource Φ z v t =
      (-I*(classicalSolution Φ z v t).1,I*(classicalSolution Φ z v t).2) := by
  simp [classicalSpectralVariationSource,coefficientVariationSource,classicalODECoefficient_apply]

/-- The actual spectral derivative of the entire solution curve is the
zero-initial forced solution of the differentiated ODE. -/
theorem hasDerivAt_classicalSolutionCurve_spectral
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    HasDerivAt (fun w : ℂ => classicalSolutionCurve Φ w v)
      (forcedSolutionCurve (classicalCoefficientCurveCLM (z,Φ))
        (classicalSpectralVariationSource Φ z v) 0) z := by
  let A := classicalCoefficientCurveCLM (z,Φ)
  let u : Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) → Curve (ℂ × ℂ) :=
    fun C => solutionCurve (realCoefficient C) v
  have hA : HasDerivAt (fun w : ℂ => classicalCoefficientCurveCLM (w,Φ))
      (classicalCoefficientCurveCLM (1,0)) z := by
    have hlin : HasFDerivAt classicalCoefficientCurveCLM classicalCoefficientCurveCLM (z,Φ) :=
      classicalCoefficientCurveCLM.hasFDerivAt
    have hpair : HasDerivAt (fun w : ℂ => (w,Φ)) ((1 : ℂ),(0 : Curve (ℂ × ℂ))) z :=
      (hasDerivAt_id z).prodMk (hasDerivAt_const z Φ)
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℂ) (F := ℂ × Curve (ℂ × ℂ))
      (E := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) z hlin hpair
  have hu : HasFDerivAt u (fderiv ℂ u A) A :=
    ((analyticOnNhd_solutionCurve_coefficient v) A (mem_univ _)).differentiableAt.hasFDerivAt
  have heq : (fun w : ℂ => classicalSolutionCurve Φ w v) =
      (fun w : ℂ => u (classicalCoefficientCurveCLM (w,Φ))) := by
    funext w
    unfold classicalSolutionCurve u
    rw [realCoefficient_classicalCoefficientCurve]
  have hbase : solutionCurve (realCoefficient A) v = classicalSolutionCurve Φ z v := by
    unfold A classicalSolutionCurve
    rw [realCoefficient_classicalCoefficientCurve]
  have hd := HasFDerivAt.comp_hasDerivAt (𝕜 := ℂ)
    (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) (E := Curve (ℂ × ℂ)) z hu hA
  change HasDerivAt (fun w : ℂ => u (classicalCoefficientCurveCLM (w,Φ)))
    ((fderiv ℂ u A) (classicalCoefficientCurveCLM (1,0))) z at hd
  rw [← heq] at hd
  unfold u at hd
  rw [fderiv_solutionCurve_coefficient_eq_forced,hbase] at hd
  exact hd

/-- Evaluation gives the spectral derivative at every point of the physical interval. -/
theorem hasDerivAt_classicalSolution_spectral
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun w : ℂ => classicalSolution Φ w v t)
      (forcedSolution (classicalCoefficientCurveCLM (z,Φ))
        (classicalSpectralVariationSource Φ z v) 0 t) z := by
  have h := (ContinuousMap.evalCLM ℂ t).hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_classicalSolutionCurve_spectral Φ z v)
  simpa only [Function.comp_def,ContinuousMap.evalCLM_apply,classicalSolutionCurve_apply,← forcedSolution_coe] using h

/-- Spectral differentiation of a linear endpoint functional has an exact
forward/dual integral, including its original sign and normalization. -/
theorem deriv_classicalEndpoint_eq_spectral_integral
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) :
    deriv (fun w : ℂ => ℓ (classicalSolution Φ w v 1)) z =
      ∫ s in (0 : ℝ)..1, -I*((classicalSolution Φ z (classicalEndpointDualInitial Φ z ℓ) s).2*
        (classicalSolution Φ z v s).1+
        (classicalSolution Φ z (classicalEndpointDualInitial Φ z ℓ) s).1*
        (classicalSolution Φ z v s).2) := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hd := (ℓ.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_classicalSolution_spectral Φ z v t)).deriv
  change deriv (fun w : ℂ => ℓ (classicalSolution Φ w v 1)) z = _ at hd
  rw [hd]
  let g := classicalSpectralVariationSource Φ z v
  let L : (ℂ × ℂ) →L[ℂ] ℂ :=
    ℓ (classicalSolution Φ z (1,0) 1) • ContinuousLinearMap.fst ℂ ℂ ℂ+
      ℓ (classicalSolution Φ z (0,1) 1) • ContinuousLinearMap.snd ℂ ℂ ℂ
  have hv : ℓ (forcedSolution (classicalCoefficientCurveCLM (z,Φ)) g 0 1) =
      L (∫ s in (0 : ℝ)..1, classicalForcedKernelIntegrand Φ g z s) := by
    rw [← classicalForcedKernelSolution_eq_forcedSolution Φ g z t]
    simp only [classicalForcedKernelSolution,classicalForcedKernelPrimitive,map_add,map_smul,L,
      smul_eq_mul,smul_apply,add_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  rw [hv,← L.intervalIntegral_comp_comm ((continuous_classicalForcedKernelIntegrand Φ g z).intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  dsimp only
  rw [classicalEndpointDualSolution_eq_columns Φ z ℓ ⟨s,hs'⟩]
  simp only [L,classicalForcedKernelIntegrand,g,smul_apply,add_apply,smul_eq_mul,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',NLS.LinearVolterra.extend,
    projIcc_of_mem _ hs',classicalSpectralVariationSource_apply,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd]
  ring

end NLS.ZakharovShabat
