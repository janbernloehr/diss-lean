import NLS.ZakharovShabat.SourcePsiOriginalQuotientBound
import NLS.ZakharovShabat.SourcePsiGapProductCompact

/-! One quotient bound on every original disc, uniformly over the
entire compact real gap product and a source neighborhood. -/
noncomputable section
open Set NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCorollary10_6Data.gap_product_allDisc_quotient_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D C)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) :
    ∃ O : Set (CoeffPair p), IsOpen O ∧ φ ∈ O ∧ ∃ Q : ℝ, 0 ≤ Q ∧
      ∀ ψ ∈ O, ∀ a ∈ sourcePeriodicGapRootSet hp hp1 φ, ∀ m : ℤ, ∀ z ∈ D m,
        ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))‖ ≤ Q := by
  let f : Coeff p × CoeffPair p → (Σ m : ℤ, D m) → ℝ :=
    fun t j => ‖sourceSingleRootQuotientJointProduct hp hp1 j.1 (j.2,t)‖
  obtain ⟨O,hO,hφ,Q,hQ,hb⟩ := exists_uniform_bound_near_compact_slice
    (sourcePeriodicGapRootSet hp hp1 φ) (isCompact_sourcePeriodicGapRootSet hp hp1 φ) φ f (by
      intro a _
      obtain ⟨U,hU,ha,Q,hQ,hb⟩ := H.local_allDisk_quotient_bound hD hV φ hφW hφV a
      exact ⟨U,hU,ha,Q,hQ,fun t ht j => hb t ht j.1 j.2 j.2.property⟩)
  exact ⟨O,hO,hφ,Q,hQ,fun ψ hψ a ha m z hz => hb ψ hψ a ha ⟨m,⟨z,hz⟩⟩⟩

end NLS.ZakharovShabat
