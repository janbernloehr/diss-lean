import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The ACTUAL zero differential and zero inverse differential of an
analytic homeomorphism form a bounded linear equivalence. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem exists_analytic_homeomorph_zero_derivative_equiv
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E ≃ₜ F) (hf : AnalyticOnNhd 𝕜 (fun x => f x) univ)
    (hi : AnalyticOnNhd 𝕜 (fun y => f.symm y) univ) (hz : f 0=0) :
    ∃ L : E ≃L[𝕜] F,(L : E →L[𝕜] F)=fderiv 𝕜 (fun x => f x) 0 ∧
      (L.symm : F →L[𝕜] E)=fderiv 𝕜 (fun y => f.symm y) 0 := by
  let A := fderiv 𝕜 (fun x => f x) 0
  let B := fderiv 𝕜 (fun y => f.symm y) 0
  have hA : HasFDerivAt (fun x => f x) A 0 := (hf 0 (mem_univ _)).differentiableAt.hasFDerivAt
  have hB : HasFDerivAt (fun y => f.symm y) B 0 := (hi 0 (mem_univ _)).differentiableAt.hasFDerivAt
  have hzi : f.symm 0=0 := by rw [←hz,f.symm_apply_apply]
  have hAi : HasFDerivAt (fun x => f x) A (f.symm 0) := by rw [hzi];exact hA
  have hBi : HasFDerivAt (fun y => f.symm y) B (f 0) := by rw [hz];exact hB
  have hAB : A.comp B=ContinuousLinearMap.id 𝕜 F := by
    have h : HasFDerivAt (fun y : F => y) (A.comp B) 0 := by
      simpa only [Function.comp_def,f.apply_symm_apply] using hAi.comp 0 hB
    exact h.unique (hasFDerivAt_id 0)
  have hBA : B.comp A=ContinuousLinearMap.id 𝕜 E := by
    have h : HasFDerivAt (fun x : E => x) (B.comp A) 0 := by
      simpa only [Function.comp_def,f.symm_apply_apply] using hBi.comp 0 hA
    exact h.unique (hasFDerivAt_id 0)
  have hleft : Function.LeftInverse B A := fun x =>
    congrArg (fun T : E →L[𝕜] E => T x) hBA
  have hright : Function.RightInverse B A := fun y =>
    congrArg (fun T : F →L[𝕜] F => T y) hAB
  exact ⟨ContinuousLinearEquiv.equivOfInverse A B hleft hright,rfl,rfl⟩

end NLS.ComplexAnalysis
