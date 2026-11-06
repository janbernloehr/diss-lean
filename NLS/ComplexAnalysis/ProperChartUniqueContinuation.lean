import NLS.ComplexAnalysis.ClosedRangeChartContinuation
import NLS.FunctionalAnalysis.ProperMapLocalUniqueness
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Separation.Hausdorff

/-! # Continuing a singleton fiber through regular preimages of a proper map -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A connected family of values of a proper map has unique preimages if
all its preimages have open charts and one of its fibers is a singleton.
No differentiability or native topology on a restricted source is needed. -/
theorem existsUnique_preimage_of_proper_of_charts [T2Space X] [PreconnectedSpace Y]
    (f : X → Z) (g : Y → Z) (hf : IsProperMap f) (hg : Continuous g)
    (hchart : ∀ y x, f x = g y → ∃ P : OpenPartialHomeomorph X Z,
      (P : X → Z) = f ∧ x ∈ P.source)
    (hstart : ∃ y, ∃! x, f x = g y) : ∀ y, ∃! x, f x = g y := by
  have hclosed : IsClosed (range f) := by
    simpa only [image_univ] using hf.isClosedMap univ isClosed_univ
  have hex : ∀ y, ∃ x, f x = g y := exists_preimage_of_closedRange_of_charts f g hg hclosed hchart
    (by obtain ⟨y,x,hx,_⟩ := hstart; exact ⟨y,x,hx⟩)
  let S : Set Y := {y | ∃! x, f x = g y}
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨a,ha,hu⟩ := hy
    obtain ⟨P,hP,haP⟩ := hchart y a ha
    have hfa : f a ∈ P.target := by rw [← hP]; exact P.map_source haP
    have hi : InjOn f P.source := hP ▸ P.injOn
    have hs : ∀ z ∈ P.target, ∃ b ∈ P.source, f b = z := by
      intro z hz
      exact ⟨P.symm z,P.map_target hz,by rw [← hP]; exact P.right_inv hz⟩
    obtain ⟨W,hW,haW,_,_,huniq⟩ :=
      NLS.FunctionalAnalysis.exists_open_global_unique_preimages_of_proper_local_chart
        hf a (fun b hb => hu b (hb.trans ha)) P.open_source haP P.open_target hfa hi hs
    exact Filter.mem_of_superset ((hW.preimage hg).mem_nhds (show g y ∈ W from ha ▸ haW))
      (fun v hv => huniq (g v) hv)
  have hcomp : IsOpen Sᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨a,ha⟩ := hex y
    have hb : ∃ b, f b = g y ∧ b ≠ a := by
      by_contra h
      apply hy
      refine ⟨a,ha,?_⟩
      intro b hbg
      by_contra hba
      exact h ⟨b,hbg,hba⟩
    obtain ⟨b,hb,hba⟩ := hb
    obtain ⟨U,V,hU,hV,haU,hbV,hUV⟩ := t2_separation hba.symm
    obtain ⟨P,hP,haP⟩ := hchart y a ha
    obtain ⟨Q,hQ,hbQ⟩ := hchart y b hb
    let W := (P '' (P.source ∩ U)) ∩ (Q '' (Q.source ∩ V))
    have hW : IsOpen W := (P.isOpen_image_source_inter hU).inter (Q.isOpen_image_source_inter hV)
    have hyW : g y ∈ W :=
      ⟨⟨a,⟨haP,haU⟩,by rw [hP]; exact ha⟩,⟨b,⟨hbQ,hbV⟩,by rw [hQ]; exact hb⟩⟩
    apply Filter.mem_of_superset ((hW.preimage hg).mem_nhds hyW)
    intro v hv hvS
    obtain ⟨c,⟨_,hcU⟩,hc⟩ := hv.1
    obtain ⟨d,⟨_,hdV⟩,hd⟩ := hv.2
    rw [hP] at hc
    rw [hQ] at hd
    obtain ⟨e,_,hu⟩ := hvS
    have he : c = d := (hu c hc).trans (hu d hd).symm
    exact Set.disjoint_left.mp hUV hcU (he ▸ hdV)
  have hall : S = univ := (show IsClopen S from ⟨isOpen_compl_iff.mp hcomp,hopen⟩).eq_univ hstart
  intro y
  exact (show y ∈ S from hall ▸ mem_univ y)

end NLS.ComplexAnalysis
