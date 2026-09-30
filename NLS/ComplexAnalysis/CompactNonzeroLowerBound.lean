import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Positive scalar lower bounds near a compact nonzero family

Continuity is needed only at the reference compact set. A positive
minimum there gives an open neighborhood with half that lower bound;
compactness puts a common closed metric thickening inside it. The
same radius and lower bound can be chosen for a finite family.
-/

namespace NLS.ComplexAnalysis
open Set Metric

/-- A scalar family nonzero and continuous on a compact reference
set keeps a common positive lower bound on a closed thickening. -/
theorem exists_positive_lower_bound_on_cthickening
    {E : Type*} [PseudoMetricSpace E] (K : Set E) (hK : IsCompact K)
    (f : E → ℂ) (hf : ∀ x ∈ K, ContinuousAt f x)
    (hne : ∀ x ∈ K, f x ≠ 0) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ x ∈ cthickening δ K, c ≤ ‖f x‖ := by
  have hcont : ContinuousOn f K := fun x hx => (hf x hx).continuousWithinAt
  obtain ⟨c,hc,hcBound⟩ := hK.exists_forall_le' hcont.norm
    (fun x hx => norm_pos_iff.mpr (hne x hx))
  let O := interior {x : E | c/2 < ‖f x‖}
  have hKO : K ⊆ O := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    exact (hf x hx).norm (Ioi_mem_nhds (by linarith [hcBound x hx]))
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open isOpen_interior hKO
  refine ⟨δ,c/2,hδ,by linarith,?_⟩
  intro x hx
  exact (interior_subset (hthick hx)).le

/-- One thickening radius and positive lower bound work for a finite
family of nonzero scalar functions on the same compact reference set. -/
theorem exists_finiteFamily_positive_lower_bound_on_cthickening
    {E ι : Type*} [PseudoMetricSpace E] (K : Set E) (hK : IsCompact K)
    (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i ∈ s, ∀ x ∈ K, ContinuousAt (f i) x)
    (hne : ∀ i ∈ s, ∀ x ∈ K, f i x ≠ 0) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ x ∈ cthickening δ K, ∀ i ∈ s, c ≤ ‖f i x‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1,1,by norm_num,by norm_num,?_⟩
      intro x hx i hi
      simp only [Finset.notMem_empty] at hi
  | @insert i s hi ih =>
      obtain ⟨δi,ci,hδi,hci,hbi⟩ := exists_positive_lower_bound_on_cthickening K hK (f i)
        (hf i (Finset.mem_insert_self i s)) (hne i (Finset.mem_insert_self i s))
      obtain ⟨δs,cs,hδs,hcs,hbs⟩ := ih
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hne j (Finset.mem_insert_of_mem hj))
      refine ⟨min δi δs,min ci cs,lt_min hδi hδs,lt_min hci hcs,?_⟩
      intro x hx j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_left ci cs).trans (hbi x (cthickening_mono (min_le_left δi δs) K hx))
      · exact (min_le_right ci cs).trans (hbs x (cthickening_mono (min_le_right δi δs) K hx) j hj)

end NLS.ComplexAnalysis
