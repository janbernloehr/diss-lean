import NLS.ZakharovShabat.SourceGenericOpenGaps
import NLS.ZakharovShabat.SourceFiniteGapDensity

/-! # All-open-gap perturbations and the meagre finite-gap locus

Generic gap opening allows arbitrarily small perturbations that open every
gap simultaneously and retain a specified open condition. Finite-gap
sources are dense by the existing approximation theorem, but meagre.
-/
noncomputable section
open Set Metric Filter Topology TopologicalSpace
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Arbitrarily small real perturbations open every actual periodic gap, while retaining
any prescribed open condition at the original source. -/
theorem exists_mem_sourceAllOpenGapRealLocus_mem_open
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (realTypeSourceSubmodule p)) (hU : IsOpen U)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∈ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ ∈ sourceAllOpenGapRealLocus hp hp1, ψ ∈ U ∧ ‖ψ.val-φ.val‖ < ε := by
  obtain ⟨ψ,hψ⟩ := (isGδ_and_dense_sourceAllOpenGapRealLocus hp hp1).2.inter_open_nonempty
    (U ∩ ball φ ε) (hU.inter isOpen_ball) ⟨φ,hφ,mem_ball_self hε⟩
  exact ⟨ψ,hψ.2,hψ.1.1,by
    change ‖ψ-φ‖ < ε
    simpa only [mem_ball,dist_eq_norm] using hψ.1.2⟩

/-- The actual finite-gap locus is meagre in the original real Banach source space. -/
theorem isMeagre_sourceFiniteGapLocus (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsMeagre (sourceFiniteGapLocus hp hp1) := by
  change (sourceFiniteGapLocus hp hp1)ᶜ ∈ residual (realTypeSourceSubmodule p)
  filter_upwards [eventually_residual_infinite_source_open_gaps hp hp1] with φ hφ
  exact hφ

/-- Finite-gap approximation and generic infinite gap opening hold in the same original topology. -/
theorem dense_and_meagre_sourceFiniteGapLocus (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Dense (sourceFiniteGapLocus hp hp1) ∧ IsMeagre (sourceFiniteGapLocus hp hp1) :=
  ⟨dense_sourceFiniteGapLocus hp hp1,isMeagre_sourceFiniteGapLocus hp hp1⟩

end NLS.ZakharovShabat
