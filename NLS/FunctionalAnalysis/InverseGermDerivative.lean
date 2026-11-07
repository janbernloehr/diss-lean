import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.Equiv

/-! Actual inverse derivatives from TWO differentiable inverse germs in
one pair of norm topologies. No global inverse is assumed. -/
noncomputable section
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem fderiv_comp_eq_id_of_inverse_germs (f : E → F) (g : F → E) (u : E)
    (hf : DifferentiableAt 𝕜 f u) (hg : DifferentiableAt 𝕜 g (f u))
    (hpoint : g (f u)=u)
    (hl : ∀ᶠ x in 𝓝 u, g (f x)=x)
    (hr : ∀ᶠ y in 𝓝 (f u), f (g y)=y) :
    (fderiv 𝕜 g (f u)).comp (fderiv 𝕜 f u)=ContinuousLinearMap.id 𝕜 E ∧
      (fderiv 𝕜 f u).comp (fderiv 𝕜 g (f u))=ContinuousLinearMap.id 𝕜 F := by
  have hlEq : (fun x => g (f x)) =ᶠ[𝓝 u] id := hl
  have hrEq : (fun y => f (g y)) =ᶠ[𝓝 (f u)] id := hr
  have hleft := (hg.hasFDerivAt.comp u hf.hasFDerivAt).congr_of_eventuallyEq hlEq.symm
  have hfg : DifferentiableAt 𝕜 f (g (f u)) := hpoint.symm ▸ hf
  have hright := (hfg.hasFDerivAt.comp (f u) hg.hasFDerivAt).congr_of_eventuallyEq hrEq.symm
  constructor
  · exact hleft.unique (hasFDerivAt_id u)
  · rw [hpoint] at hright
    exact hright.unique (hasFDerivAt_id (f u))

/-- The actual forward derivative is a bounded linear equivalence, whose
inverse is the actual derivative of the specified local inverse germ. -/
theorem exists_fderiv_equiv_of_inverse_germs (f : E → F) (g : F → E) (u : E)
    (hf : DifferentiableAt 𝕜 f u) (hg : DifferentiableAt 𝕜 g (f u))
    (hpoint : g (f u)=u)
    (hl : ∀ᶠ x in 𝓝 u, g (f x)=x)
    (hr : ∀ᶠ y in 𝓝 (f u), f (g y)=y) :
    ∃ e : E ≃L[𝕜] F, e.toContinuousLinearMap=fderiv 𝕜 f u ∧
      e.symm.toContinuousLinearMap=fderiv 𝕜 g (f u) := by
  obtain ⟨hl',hr'⟩ := fderiv_comp_eq_id_of_inverse_germs f g u hf hg hpoint hl hr
  exact ⟨ContinuousLinearEquiv.equivOfInverse' (fderiv 𝕜 f u) (fderiv 𝕜 g (f u)) hr' hl',rfl,rfl⟩

end NLS.FunctionalAnalysis
