import Mathlib.Topology.Compactness.Compact

/-! A locally uniform natural-number threshold becomes uniform on a compact
parameter space. The conclusion retains every larger threshold. -/
noncomputable section
open Set
namespace NLS

/-- Compactness chooses one common threshold before all parameters and all
larger indices, when the assertion holds locally uniformly. -/
theorem exists_uniform_nat_threshold_on_compact
    {T : Type*} [TopologicalSpace T] [CompactSpace T] (P : T → ℕ → Prop)
    (h : ∀ t, ∃ N : ℕ, ∃ U : Set T, IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ M : ℕ, N ≤ M → P s M) :
    ∃ N : ℕ, ∀ t, ∀ M : ℕ, N ≤ M → P t M := by
  classical
  choose N U ho hm hb using h
  obtain ⟨J,hJ⟩ := isCompact_univ.elim_finite_subcover U ho
    (fun t _ => mem_iUnion.mpr ⟨t,hm t⟩)
  refine ⟨J.sup N,fun t M hM => ?_⟩
  obtain ⟨s,hs,ht⟩ := mem_iUnion₂.mp (hJ (mem_univ t))
  exact hb s t ht M ((Finset.le_sup hs).trans hM)

end NLS
