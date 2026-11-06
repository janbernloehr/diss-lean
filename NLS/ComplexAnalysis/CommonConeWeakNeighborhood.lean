import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Connected.LocallyConnected

/-! An open neighborhood of an ENTIRE convex cone can be restricted so
its intersection with a smaller weak-norm ball stays in ONE connected
component of the original common domain. The neighborhood is independent
of every analytic component index. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A single open neighborhood of the whole cone supports simultaneous
analytic continuation from zero through a prescribed smaller weak ball. -/
theorem exists_open_cone_weak_component_neighborhood
    (J : E →L[ℂ] F) (C U : Set E) (hC : Convex ℝ C) (h0 : (0 : E)∈C)
    (hU : IsOpen U) (hCU : C⊆U) (r : ℝ) (hr : 0<r) :
    ∃ V : Set E, IsOpen V ∧ C⊆V ∧ V⊆U ∧
      V∩J ⁻¹' ball (0 : F) (r/2)⊆connectedComponentIn (U∩J ⁻¹' ball (0 : F) r) 0 := by
  let W := connectedComponentIn (U∩J ⁻¹' ball (0 : F) r) 0
  have hW : IsOpen W := (hU.inter (isOpen_ball.preimage J.continuous)).connectedComponentIn
  have hpre : Convex ℝ (J ⁻¹' ball (0 : F) r) :=
    (convex_ball (0 : F) r).linear_preimage (J.restrictScalars ℝ).toLinearMap
  have hsmall : C∩J ⁻¹' ball (0 : F) r⊆W :=
    (hC.inter hpre).isPreconnected.subset_connectedComponentIn
      ⟨h0,by simpa only [mem_preimage,map_zero] using mem_ball_self hr⟩
      (fun _ ha => ⟨hCU ha.1,ha.2⟩)
  let V := U∩(W∪{x : E | r/2<‖J x‖})
  refine ⟨V,hU.inter (hW.union (isOpen_lt continuous_const J.continuous.norm)),?_,inter_subset_left,?_⟩
  · intro x hx
    refine ⟨hCU hx,?_⟩
    by_cases hnorm : r/2<‖J x‖
    · exact Or.inr hnorm
    · exact Or.inl (hsmall ⟨hx,mem_ball_zero_iff.mpr (by linarith)⟩)
  · intro x hx
    rcases hx.1.2 with h | h
    · exact h
    · have hn := mem_ball_zero_iff.mp hx.2
      exact (not_lt_of_ge hn.le h).elim

end NLS.ComplexAnalysis
