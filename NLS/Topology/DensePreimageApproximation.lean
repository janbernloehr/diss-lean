import Mathlib.Topology.Sequences

/-! Density in the actual source topology from approximating sequences
whose images eventually lie in a prescribed set. No topology or continuity
assumption on the image space is needed. -/
noncomputable section
open Set Filter Topology
namespace NLS.Topology

theorem dense_preimage_of_approximating_sequences {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (S : Set Y)
    (h : ∀ x : X, ∃ v : ℕ → X, Tendsto v atTop (𝓝 x) ∧ ∀ᶠ n in atTop, f (v n) ∈ S) :
    Dense (f ⁻¹' S) := by
  intro x
  obtain ⟨v,hv,hm⟩ := h x
  exact mem_closure_of_tendsto hv hm

end NLS.Topology
