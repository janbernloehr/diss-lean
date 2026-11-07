import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Hausdorff

/-! A closed graph detects continuity when the target is compact Hausdorff. -/
noncomputable section
open Set Topology
namespace NLS

/-- Compactness of the target suffices; no compactness of the domain is needed. -/
theorem continuous_iff_isClosed_graph_compact_target
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] (f : X → Y) :
    Continuous f ↔ IsClosed {p : X × Y | f p.1 = p.2} := by
  constructor
  · intro hf
    exact isClosed_eq (hf.comp continuous_fst) continuous_snd
  · intro hg
    apply continuous_iff_isClosed.mpr
    intro s hs
    have he : f ⁻¹' s = Prod.fst ''
        ({p : X × Y | f p.1 = p.2} ∩ Prod.snd ⁻¹' s) := by
      ext x
      constructor
      · intro hx
        exact ⟨(x, f x), ⟨rfl, hx⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hxy, hy⟩, rfl⟩
        change f x = y at hxy
        change f x ∈ s
        rwa [hxy]
    rw [he]
    exact isClosedMap_fst_of_compactSpace _ (hg.inter (hs.preimage continuous_snd))

end NLS
