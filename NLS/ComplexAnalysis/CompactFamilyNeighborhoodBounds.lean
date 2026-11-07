import NLS.ComplexAnalysis.CompactSliceLocalBounds
import Mathlib.Topology.MetricSpace.Thickening

/-! Common open neighborhoods and closed thickenings for an arbitrarily
indexed family locally bounded before all indices near a compact set.
The neighborhood stays inside the original open input domain. -/
noncomputable section
open Set Metric
open scoped Classical
namespace NLS.ComplexAnalysis

theorem exists_open_uniform_bound_near_compact
    {E F ι : Type*} [TopologicalSpace E] [SeminormedAddCommGroup F]
    (K U : Set E) (hK : IsCompact K) (f : ι → E → F)
    (hlocal : ∀ x ∈ K, ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ O ⊆ U ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ i : ι, ∀ y ∈ O, ‖f i y‖ ≤ L) :
    ∃ O : Set E, IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ i : ι, ∀ y ∈ O, ‖f i y‖ ≤ L := by
  choose O ho hx hsub L hL hb using fun x : K => hlocal x x.property
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover O ho (by
    intro x hxK
    exact mem_iUnion.mpr ⟨⟨x,hxK⟩,hx ⟨x,hxK⟩⟩)
  let J : Set E := ⋃ x ∈ s, O x
  have hJ : IsOpen J := isOpen_biUnion (fun x _ => ho x)
  refine ⟨J,hJ,hs,?_,∑ x ∈ s, L x,Finset.sum_nonneg (fun x _ => hL x),?_⟩
  · intro y hy
    obtain ⟨x,_,hxy⟩ := mem_iUnion₂.mp hy
    exact hsub x hxy
  · intro i y hy
    obtain ⟨x,hxs,hxy⟩ := mem_iUnion₂.mp hy
    exact (hb x i y hxy).trans (Finset.single_le_sum (fun x _ => hL x) hxs)

theorem exists_cthickening_uniform_bound_near_compact
    {E F ι : Type*} [PseudoMetricSpace E] [SeminormedAddCommGroup F]
    (K U : Set E) (hK : IsCompact K) (f : ι → E → F)
    (hlocal : ∀ x ∈ K, ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ O ⊆ U ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ i : ι, ∀ y ∈ O, ‖f i y‖ ≤ L) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧ cthickening δ K ⊆ U ∧
      ∀ i : ι, ∀ y ∈ cthickening δ K, ‖f i y‖ ≤ L := by
  obtain ⟨O,hO,hKO,hOU,L,hL,hbound⟩ := exists_open_uniform_bound_near_compact K U hK f hlocal
  obtain ⟨δ,hδ,ht⟩ := hK.exists_cthickening_subset_open hO hKO
  exact ⟨δ,L,hδ,hL,ht.trans hOU,fun i y hy => hbound i y (ht hy)⟩

end NLS.ComplexAnalysis
