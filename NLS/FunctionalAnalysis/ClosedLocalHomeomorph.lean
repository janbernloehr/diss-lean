import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff

/-! # A closed local homeomorphism with a singleton fiber

On a connected target, the locus of fibers with at most one point is both
open and closed. Closedness of the map controls the complement of a local
inverse neighborhood; separated source neighborhoods make multiple fibers
persist. A single singleton fiber therefore gives global bijectivity.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]

/-- For a closed local homeomorphism, fibers with at most one point form
an open and closed subset of the target. Empty fibers are included. -/
theorem isClopen_singleFiber_locus (f : X → Y) (hl : IsLocalHomeomorph f) (hc : IsClosedMap f) :
    IsClopen {y : Y | ∀ x x' : X, f x = y → f x' = y → x = x'} := by
  let S : Set Y := {y | ∀ x x' : X, f x = y → f x' = y → x = x'}
  have ho : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    by_cases hfiber : ∃ x : X, f x = y
    · obtain ⟨x,hx⟩ := hfiber
      obtain ⟨e,hxe,he⟩ := hl x
      have hinj : InjOn f e.source := by rw [he]; exact e.injOn
      have hyU : y ∈ (f '' e.sourceᶜ)ᶜ := by
        rintro ⟨u,hu,huEq⟩
        exact hu ((hy u x huEq hx) ▸ hxe)
      apply mem_of_superset ((hc _ e.open_source.isClosed_compl).isOpen_compl.mem_nhds hyU)
      intro z hz u v hu hv
      have huU : u ∈ e.source := by
        by_contra hn
        exact hz ⟨u,hn,hu⟩
      have hvU : v ∈ e.source := by
        by_contra hn
        exact hz ⟨v,hn,hv⟩
      exact hinj huU hvU (hu.trans hv.symm)
    · have hyU : y ∈ (f '' (univ : Set X))ᶜ := by
        rintro ⟨x,_,hx⟩
        exact hfiber ⟨x,hx⟩
      apply mem_of_superset ((hc _ isClosed_univ).isOpen_compl.mem_nhds hyU)
      intro z hz u v hu _
      exact (hz ⟨u,mem_univ _,hu⟩).elim
  have hbad : IsOpen Sᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hne : ∃ x x' : X, f x = y ∧ f x' = y ∧ x ≠ x' := by
      by_contra hn
      apply hy
      intro x x' hx hx'
      by_contra hxx'
      exact hn ⟨x,x',hx,hx',hxx'⟩
    obtain ⟨x,x',hx,hx',hne⟩ := hne
    obtain ⟨U,V,hU,hV,hxU,hxV,hUV⟩ := t2_separation hne
    have hyUV : y ∈ f '' U ∩ f '' V := ⟨⟨x,hxU,hx⟩,⟨x',hxV,hx'⟩⟩
    apply mem_of_superset (((hl.isOpenMap _ hU).inter (hl.isOpenMap _ hV)).mem_nhds hyUV)
    rintro z ⟨⟨u,hu,huz⟩,⟨v,hv,hvz⟩⟩ hz
    have he : u = v := hz u v huz hvz
    exact Set.disjoint_left.mp hUV hu (he.symm ▸ hv)
  exact ⟨isOpen_compl_iff.mp hbad,ho⟩

/-- One singleton fiber makes a closed local homeomorphism bijective over
a preconnected target. This does not require local compactness or finite
dimensionality of either space. -/
theorem bijective_of_closed_localHomeomorph_singleton_fiber [PreconnectedSpace Y]
    (f : X → Y) (hl : IsLocalHomeomorph f) (hc : IsClosedMap f) (x₀ : X)
    (hzero : ∀ x : X, f x = f x₀ → x = x₀) : Function.Bijective f := by
  have hS := (isClopen_singleFiber_locus f hl hc).eq_univ
    (show {y : Y | ∀ x x' : X, f x = y → f x' = y → x = x'}.Nonempty from
      ⟨f x₀,fun x x' hx hx' => (hzero x hx).trans (hzero x' hx').symm⟩)
  have hr : range f = univ := by
    have hcl : IsClopen (range f) := by
      simpa only [image_univ] using
        (show IsClopen (f '' (univ : Set X)) from ⟨hc _ isClosed_univ,hl.isOpenMap _ isOpen_univ⟩)
    exact hcl.eq_univ ⟨f x₀,⟨x₀,rfl⟩⟩
  refine ⟨?_,range_eq_univ.mp hr⟩
  intro x x' he
  have hmem : f x ∈ {y : Y | ∀ u v : X, f u = y → f v = y → u = v} := by rw [hS]; trivial
  exact hmem x x' rfl he.symm

end NLS.FunctionalAnalysis
