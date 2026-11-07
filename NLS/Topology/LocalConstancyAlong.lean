import Mathlib.Topology.LocallyConstant.Basic

/-! Relative local constancy persists along continuous curves from a
preconnected parameter space; no connectedness of the ambient fiber is
required. -/
noncomputable section
open Set Filter Topology
namespace NLS.Topology

/-- A function locally constant relative to a set is constant along every
continuous preconnected family in that set. -/
theorem eq_along_continuous_of_relative_local_constancy
    {X Y A : Type*} [TopologicalSpace X] [TopologicalSpace A] [PreconnectedSpace A]
    (K : Set X) (F : X → Y)
    (hl : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, y ∈ K → F y=F x)
    (γ : A → X) (hc : Continuous γ) (hm : ∀ a, γ a ∈ K) (a b : A) : F (γ a)=F (γ b) := by
  have hloc : IsLocallyConstant (fun c => F (γ c)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro c
    obtain ⟨U,hU,hcU,hconst⟩ := hl (γ c) (hm c)
    filter_upwards [hc.continuousAt.eventually (hU.mem_nhds hcU)] with d hd
    exact hconst (γ d) hd (hm d)
  exact hloc.apply_eq_of_preconnectedSpace a b

end NLS.Topology
