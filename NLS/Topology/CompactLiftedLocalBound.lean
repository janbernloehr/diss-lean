import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Local bounds for a family lifted through a compact parameter set
become one bound on one open neighborhood of the whole compact set. -/
noncomputable section
open Set
namespace NLS.Topology

/-- The indexed objects may carry a separate constraint. Only their
images in the compact parameter space determine which local estimate applies. -/
theorem exists_open_uniform_lifted_bound {A X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : A → X) (g : A → ℝ) (S : Set A)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ S, f a ∈ U → g a ≤ C) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ S, f a ∈ U → g a ≤ C := by
  classical
  choose U ho hx C hC hb using fun x : K => hlocal x x.property
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover U ho (by
    intro x hxK
    exact mem_iUnion.mpr ⟨⟨x,hxK⟩,hx ⟨x,hxK⟩⟩)
  refine ⟨⋃ x ∈ J, U x,isOpen_biUnion (fun x _ => ho x),hJ,
    ∑ x ∈ J, C x,Finset.sum_nonneg (fun x _ => hC x),?_⟩
  intro a ha hf
  obtain ⟨x,hxJ,hfx⟩ := mem_iUnion₂.mp hf
  exact (hb x a ha hfx).trans (Finset.single_le_sum (fun x _ => hC x) hxJ)

end NLS.Topology
