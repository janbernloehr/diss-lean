import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Connected.Clopen

/-! # Continuing a closed range along a connected parameter space

Local open charts at every preimage make the lifted range open. Closed
range makes it closed, so one initial preimage reaches every parameter.
-/
noncomputable section
open Set
namespace NLS.ComplexAnalysis
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Local charts at all existing preimages and closed range imply
existence along every connected family containing one attained value. -/
theorem exists_preimage_of_closedRange_of_charts [PreconnectedSpace Y]
    (f : X → Z) (g : Y → Z) (hg : Continuous g) (hf : IsClosed (range f))
    (hchart : ∀ y x, f x = g y → ∃ P : OpenPartialHomeomorph X Z,
      (P : X → Z) = f ∧ x ∈ P.source)
    (hstart : ∃ y x, f x = g y) : ∀ y, ∃ x, f x = g y := by
  let S := g ⁻¹' range f
  have hclosed : IsClosed S := hf.preimage hg
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨x,hx⟩ := hy
    obtain ⟨P,hP,hxP⟩ := hchart y x hx
    have hyt : g y ∈ P.target := by rw [← hx,← hP]; exact P.map_source hxP
    apply Filter.mem_of_superset ((P.open_target.preimage hg).mem_nhds hyt)
    intro v hv
    exact ⟨P.symm (g v),by rw [← hP]; exact P.right_inv hv⟩
  have hnonempty : S.Nonempty := by
    obtain ⟨y,x,hx⟩ := hstart
    exact ⟨y,x,hx⟩
  have hall : S = univ := (show IsClopen S from ⟨hclosed,hopen⟩).eq_univ hnonempty
  intro y
  have hy : y ∈ S := hall ▸ mem_univ y
  exact hy

end NLS.ComplexAnalysis
