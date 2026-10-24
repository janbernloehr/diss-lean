import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # The graph of the double adjoint

Hilbert-space orthogonal separation identifies the double adjoint relation
with the closure of the original graph.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The double adjoint relation is the topological closure of a linear relation. -/
theorem submodule_adjoint_adjoint (g : Submodule 𝕜 (E × F)) :
    g.adjoint.adjoint = g.topologicalClosure := by
  let J : (E × F) ≃L[𝕜] WithLp 2 (E × F) :=
    (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm
  let P : Submodule 𝕜 (WithLp 2 (E × F)) := g.map J.toLinearMap
  have hc (x : E × F) : J x ∈ P.topologicalClosure ↔ x ∈ g.topologicalClosure := by
    change J x ∈ closure (J '' (g : Set (E × F))) ↔ x ∈ closure (g : Set (E × F))
    have he : J '' closure (g : Set (E × F)) = closure (J '' (g : Set (E × F))) := by
      simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using! J.toHomeomorph.image_closure (g : Set (E × F))
    rw [← he]
    exact J.injective.mem_set_image
  ext x
  rw [← hc,← P.orthogonal_orthogonal_eq_closure]
  constructor
  · intro hx
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    have hm : (-y.ofLp.2,y.ofLp.1) ∈ g.adjoint := by
      apply (Submodule.mem_adjoint_iff _ _).mpr
      intro a b hab
      have h := ((Submodule.mem_orthogonal _ _).mp hy) (J (a,b)) ⟨(a,b),hab,rfl⟩
      have hn := congrArg Neg.neg h
      simpa [J,WithLp.prod_inner_apply,inner_neg_right,neg_add_rev,sub_eq_add_neg] using hn
    have h := (Submodule.mem_adjoint_iff _ _).mp hx (-y.ofLp.2) y.ofLp.1 hm
    simpa [J,WithLp.prod_inner_apply,inner_neg_left,sub_eq_add_neg] using h
  · intro hx
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro a b hab
    have hm : J (b,-a) ∈ P.orthogonal := by
      apply (Submodule.mem_orthogonal _ _).mpr
      intro y hy
      obtain ⟨z,hz,rfl⟩ := hy
      have h := (Submodule.mem_adjoint_iff _ _).mp hab z.1 z.2 hz
      have hn := congrArg Neg.neg h
      simpa [J,WithLp.prod_inner_apply,inner_neg_right,sub_eq_add_neg,add_comm] using hn
    have h := ((Submodule.mem_orthogonal _ _).mp hx) (J (b,-a)) hm
    simpa [J,WithLp.prod_inner_apply,inner_neg_left,sub_eq_add_neg] using h

/-- A densely defined operator with dense adjoint domain has double
adjoint equal to its actual graph closure. -/
theorem adjoint_adjoint_eq_closure {T : E →ₗ.[𝕜] F}
    (hT : Dense (T.domain : Set E)) (ha : Dense (T.adjoint.domain : Set F))
    (hc : T.IsClosable) : T.adjoint.adjoint = T.closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint ha,
    LinearPMap.adjoint_graph_eq_graph_adjoint hT,submodule_adjoint_adjoint,
    hc.graph_closure_eq_closure_graph]

end NLS.FunctionalAnalysis
