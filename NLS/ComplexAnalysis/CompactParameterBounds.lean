import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Complex.Liouville

/-!
# Local uniform bounds over compact spectral sets

A jointly continuous scalar family is uniformly bounded on a fixed compact
spectral set after restricting the parameter to one open neighborhood.
-/

namespace NLS.ComplexAnalysis
open Set

theorem exists_local_uniform_bound_on_compact {E : Type*} [TopologicalSpace E]
    (f : ℂ × E → ℂ) (hf : Continuous f) (K : Set ℂ) (hK : IsCompact K) (x : E) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ U, ∀ z ∈ K, ‖f (z,y)‖ ≤ B := by
  obtain ⟨t, htK, hto, htb⟩ :=
    Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
      (hK.prod isCompact_singleton) isOpen_univ (subset_univ _) hf.continuousOn
  obtain ⟨W, U, _, hUo, _, hUx, hWU⟩ :=
    generalized_tube_lemma hK isCompact_singleton hto htK
  obtain ⟨B, hB, hb⟩ := htb.exists_pos_norm_le
  refine ⟨U, hUo, hUx (mem_singleton x), B, hB.le, fun y hy z hz => ?_⟩
  apply hb
  exact ⟨(z,y), hWU ⟨(by aesop),hy⟩, rfl⟩

end NLS.ComplexAnalysis
