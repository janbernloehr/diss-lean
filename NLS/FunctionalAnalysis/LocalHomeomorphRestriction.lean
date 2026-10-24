import Mathlib.Topology.IsLocalHomeomorph

/-! # Restricting local homeomorphisms to output subspaces

An arbitrary target subset inherits a local homeomorphism from its full
preimage. This supplies the topological restriction needed for finite
spectral support without requiring the target subset to be open.
-/
noncomputable section
open Set Topology
namespace NLS.FunctionalAnalysis
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open map restricts to an open map on the full preimage of every target subset. -/
theorem isOpenMap_restrictPreimage {f : X → Y} (hf : IsOpenMap f) (S : Set Y) :
    IsOpenMap (S.restrictPreimage f) := by
  intro U hU
  obtain ⟨V,hV,rfl⟩ := isOpen_induced_iff.mp hU
  have he : (S.restrictPreimage f) '' (Subtype.val ⁻¹' V) =
      Subtype.val ⁻¹' (f '' V) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x.val,hx,congrArg Subtype.val hxy⟩
    · rintro ⟨x,hx,hxy⟩
      refine ⟨⟨x,?_⟩,hx,Subtype.ext hxy⟩
      change f x ∈ S
      rw [hxy]
      exact y.property
  rw [he]
  exact continuous_subtype_val.isOpen_preimage _ (hf V hV)

/-- A local homeomorphism restricts to the full preimage of any target subset. -/
theorem isLocalHomeomorph_restrictPreimage {f : X → Y}
    (hf : IsLocalHomeomorph f) (S : Set Y) :
    IsLocalHomeomorph (S.restrictPreimage f) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨e,hx,he⟩ := hf x.val
  let U : Set (f ⁻¹' S) := Subtype.val ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage continuous_subtype_val
  refine ⟨U,hU.mem_nhds hx,?_⟩
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨hf.continuous.restrictPreimage.comp continuous_subtype_val,?_,
    (isOpenMap_restrictPreimage hf.isOpenMap S).comp hU.isOpenMap_subtype_val⟩
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply e.injOn a.property b.property
  have h := congrArg (fun y : S => y.val) hab
  change f a.val.val = f b.val.val at h
  exact (congrFun he a.val.val).symm.trans (h.trans (congrFun he b.val.val))

end NLS.FunctionalAnalysis
