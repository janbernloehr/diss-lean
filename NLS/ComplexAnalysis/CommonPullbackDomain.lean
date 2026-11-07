import Mathlib.Topology.ContinuousOn

/-! An opaque common domain for a locally continuous parameterization
and a second continuous inclusion. -/
set_option autoImplicit false
open Set
namespace NLS

theorem exists_open_common_pullback_domain
    {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    (U : Set E) (hU : IsOpen U) (x : E) (hx : x∈U)
    (f : E → F) (hf : ContinuousOn f U) (V : Set F) (hV : IsOpen V) (hfx : f x∈V)
    (g : E → G) (hg : Continuous g) (W : Set G) (hW : IsOpen W) (hgx : g x∈W) :
    ∃ T : Set E, IsOpen T ∧ x∈T ∧ T⊆U ∧
      (∀ y∈T, f y∈V) ∧ ∀ y∈T, g y∈W := by
  let T := (U∩f ⁻¹' V)∩g ⁻¹' W
  exact ⟨T,(hf.isOpen_inter_preimage hU hV).inter (hW.preimage hg),⟨⟨hx,hfx⟩,hgx⟩,
    (fun _ hy => hy.1.1),(fun _ hy => hy.1.2),fun _ hy => hy.2⟩

end NLS
