import Mathlib.Topology.Maps.Proper.Basic

/-! # Global uniqueness near a singleton fiber of a proper map -/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

theorem exists_open_global_unique_preimages_of_proper_local_chart
    {f : E → F} (hf : IsProperMap f) (a : E)
    (hfiber : ∀ b, f b = f a → b = a)
    {U : Set E} {V : Set F} (hU : IsOpen U) (ha : a ∈ U)
    (hV : IsOpen V) (hfa : f a ∈ V) (hi : InjOn f U)
    (hs : ∀ z ∈ V, ∃ b ∈ U, f b = z) :
    ∃ W : Set F, IsOpen W ∧ f a ∈ W ∧ W ⊆ V ∧
      (∀ b, f b ∈ W → b ∈ U) ∧ ∀ z ∈ W, ∃! b, f b = z := by
  let W := V ∩ (f '' Uᶜ)ᶜ
  have hw (b : E) (hb : f b ∈ W) : b ∈ U := by
    by_contra hn
    exact hb.2 ⟨b,hn,rfl⟩
  refine ⟨W,hV.inter (hf.isClosedMap _ hU.isClosed_compl).isOpen_compl,?_,inter_subset_left,hw,?_⟩
  · refine ⟨hfa,?_⟩
    rintro ⟨b,hb,he⟩
    exact hb (hfiber b he ▸ ha)
  · intro z hz
    obtain ⟨b,hb,he⟩ := hs z hz.1
    refine ⟨b,he,?_⟩
    intro c hc
    have hcU := hw c (hc ▸ hz)
    exact hi hcU hb (hc.trans he.symm)

end NLS.FunctionalAnalysis
