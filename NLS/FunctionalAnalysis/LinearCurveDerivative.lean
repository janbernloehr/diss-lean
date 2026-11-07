import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! Real curve differentiation through bounded linear and differentiable
Banach-space maps, retaining the full norm derivative. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_clm_comp (L : E →L[ℝ] F) (γ : ℝ → E) (v : E) (t : ℝ)
    (hγ : HasDerivAt γ v t) : HasDerivAt (fun s => L (γ s)) (L v) t :=
  L.hasFDerivAt.comp_hasDerivAt t hγ

theorem hasDerivAt_differentiable_comp (f : E → F) (γ : ℝ → E) (v : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => f (γ s)) ((fderiv ℝ f (γ t)) v) t :=
  hf.hasFDerivAt.comp_hasDerivAt t hγ

end NLS.FunctionalAnalysis
