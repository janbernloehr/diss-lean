import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-! Independent one-coordinate updates inside a compact set realize every
simultaneous prescribed coordinate value. Only scalar coordinate continuity
is needed; neither global injectivity nor a countable index set is assumed. -/
noncomputable section
open Set
namespace NLS.Topology
variable {X I Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

omit [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] in
theorem exists_finite_coordinate_match (K : Set X) (hne : K.Nonempty)
    (f : X → I → Y) (z : I → Y)
    (hstep : ∀ i x, x ∈ K → ∃ y ∈ K, f y i=z i ∧ ∀ j, j ≠ i → f y j=f x j)
    (J : Finset I) : ∃ x ∈ K, ∀ i ∈ J, f x i=z i := by
  classical
  induction J using Finset.induction_on with
  | empty => obtain ⟨x,hx⟩ := hne; exact ⟨x,hx,fun _ hi => False.elim (Finset.notMem_empty _ hi)⟩
  | @insert i J hi ih =>
    obtain ⟨x,hx,hJ⟩ := ih
    obtain ⟨y,hy,hyi,hyother⟩ := hstep i x hx
    refine ⟨y,hy,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hyi
    · rw [hyother j (by intro he; subst j; exact hi hj)]
      exact hJ j hj

theorem exists_compact_coordinate_match (K : Set X) (hK : IsCompact K) (hne : K.Nonempty)
    (f : X → I → Y) (hf : ∀ i, Continuous (fun x => f x i)) (z : I → Y)
    (hstep : ∀ i x, x ∈ K → ∃ y ∈ K, f y i=z i ∧ ∀ j, j ≠ i → f y j=f x j) :
    ∃ x ∈ K, ∀ i, f x i=z i := by
  obtain ⟨x,hxK,hx⟩ := hK.inter_iInter_nonempty (fun i => {x | f x i=z i})
    (fun i => isClosed_eq (hf i) continuous_const) (by
      intro J
      obtain ⟨x,hx,hJ⟩ := exists_finite_coordinate_match K hne f z hstep J
      exact ⟨x,hx,mem_iInter₂.mpr hJ⟩)
  exact ⟨x,hxK,mem_iInter.mp hx⟩

end NLS.Topology
