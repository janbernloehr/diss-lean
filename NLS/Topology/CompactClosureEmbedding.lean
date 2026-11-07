import Mathlib.Topology.Separation.Hausdorff

/-! Continuity and injectivity on a compact closure give an embedding
on the original, possibly nonclosed subset. -/
noncomputable section
open Set
namespace NLS.Topology

/-- Restriction to an arbitrary subset of a compact closure is an embedding
whenever the supplied map is continuous and injective on that closure. -/
theorem isEmbedding_restriction_of_compact_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (A : Set X) (hA : IsCompact (closure A))
    (hf : Continuous (fun x : closure A => f x.val))
    (hi : InjOn f (closure A)) :
    Topology.IsEmbedding (fun x : A => f x.val) := by
  let K := closure A
  let : CompactSpace K := isCompact_iff_compactSpace.mp hA
  have he : Topology.IsClosedEmbedding (fun x : K => f x.val) :=
    hf.isClosedEmbedding (fun x y hxy => Subtype.ext (hi x.property y.property hxy))
  let j : A → K := fun x => ⟨x.val,subset_closure x.property⟩
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp Topology.IsEmbedding.subtypeVal
  exact he.isEmbedding.comp hj

end NLS.Topology
