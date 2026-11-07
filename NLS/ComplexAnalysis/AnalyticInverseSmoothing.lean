import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The SAME actual inverse gains regularity from a forward remainder
and compatible TRUE linearizations at two native orders. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem exists_analytic_inverse_smoothing
    {𝕜 E₀ E₁ F₀ F₁ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (I : E₁ →L[𝕜] E₀) (J : F₁ →L[𝕜] F₀)
    (L₀ : E₀ ≃L[𝕜] F₀) (L₁ : E₁ ≃L[𝕜] F₁)
    (hc : ∀ x : E₁,J (L₁ x)=L₀ (I x))
    (f : E₀ ≃ₜ F₀) (hi : AnalyticOnNhd 𝕜 (fun z => f.symm z) univ)
    (R : E₀ → F₁) (hRa : AnalyticOnNhd 𝕜 R univ)
    (hf : ∀ q,f q=L₀ q+J (R q)) :
    ∃ S : F₀ → E₁,AnalyticOnNhd 𝕜 S univ ∧
      ∀ z,f.symm z-L₀.symm z=I (S z) := by
  let S := fun z => -L₁.symm (R (f.symm z))
  have hSa : AnalyticOnNhd 𝕜 S univ := fun z _ =>
    (((L₁.symm : F₁ →L[𝕜] E₁).analyticAt _).comp
      ((hRa _ (mem_univ _)).comp (hi z (mem_univ _)))).neg
  refine ⟨S,hSa,?_⟩
  intro z
  apply L₀.injective
  have he : z=L₀ (f.symm z)+J (R (f.symm z)) := (f.apply_symm_apply z).symm.trans (hf _)
  rw [map_sub,L₀.apply_symm_apply,←hc]
  change L₀ (f.symm z)-z=J (L₁ (-L₁.symm (R (f.symm z))))
  rw [map_neg,L₁.apply_symm_apply,map_neg]
  calc
    L₀ (f.symm z)-z=L₀ (f.symm z)-(L₀ (f.symm z)+J (R (f.symm z))) :=
      congrArg (fun w : F₀ => L₀ (f.symm z)-w) he
    _= -J (R (f.symm z)) := by abel

end NLS.ComplexAnalysis
