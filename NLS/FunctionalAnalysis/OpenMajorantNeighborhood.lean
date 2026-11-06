import Mathlib.Topology.Basic

/-! Restrict an open neighborhood carrying a witness bound to an
additional open domain, without changing the witness or its bound. -/
namespace NLS.FunctionalAnalysis
open Set

structure OpenMajorantNeighborhood (E : Type*) [TopologicalSpace E]
    {B : Type*} (S : Set E) (Good : E → B → Prop) where
  source : Set E
  source_open : IsOpen source
  subset : source ⊆ S
  constant : B
  good : ∀ x ∈ source, Good x constant

theorem exists_openMajorantNeighborhood {E B : Type*} [TopologicalSpace E]
    (S : Set E) (hS : IsOpen S) (Good : E → B → Prop)
    (q : E) (hq : q ∈ S) (V : Set E) (hV : IsOpen V) (hqV : q ∈ V)
    (M : B) (hgood : ∀ x ∈ V, Good x M) :
    ∃ A : OpenMajorantNeighborhood E S Good, q ∈ A.source :=
  ⟨⟨V ∩ S,hV.inter hS,inter_subset_right,M,fun x hx => hgood x hx.1⟩,⟨hqV,hq⟩⟩

theorem OpenMajorantNeighborhood.mapsTo_preimage {E F B : Type*} [TopologicalSpace E]
    (f : E → F) (S : Set F) (Good : E → B → Prop)
    (A : OpenMajorantNeighborhood E (f ⁻¹' S) Good) : MapsTo f A.source S :=
  fun _ hx => A.subset hx

theorem mem_preimage_of_apply_mem {E F : Type*} (f : E → F) (S : Set F)
    (x : E) (h : f x ∈ S) : x ∈ f ⁻¹' S := h

end NLS.FunctionalAnalysis
