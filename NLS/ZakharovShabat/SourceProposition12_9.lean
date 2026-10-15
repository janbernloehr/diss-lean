import NLS.ZakharovShabat.SourceCorollary12_8
import NLS.ZakharovShabat.SourcePsiOriginalImplicit

/-!
# Proposition 12.9 on the original real domain

For every finite p above one, the original equation has a unique global
real analytic solution with graph in the original deleted domain.
The roots lie in their actual periodic gaps. The unchanged W and the
preceding Jacobian isomorphisms are retained.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Proposition 12.9 with the actual equation, original domains, and preceding data. -/
structure SourceProposition12_9Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceCorollary12_8Data hp hp1 W
  solution : ∀ n : ℤ, ∃! s : realTypeSourceSubmodule p → RealDeletedCoeff p n,
    AnalyticOnNhd ℝ s univ ∧ ∀ φ, SourcePsiOriginalRealSolution hp hp1 n φ (s φ)
  canonical : ∀ n : ℤ, ∀ φ : realTypeSourceSubmodule p,
    SourcePsiOriginalRealSolution hp hp1 n φ (sourcePsiOriginalRootReal hp hp1 n φ)
  unique : ∀ n : ℤ, ∀ φ : realTypeSourceSubmodule p, ∀ a : RealDeletedCoeff p n,
    SourcePsiOriginalRealSolution hp hp1 n φ a → a = sourcePsiOriginalRootReal hp hp1 n φ
  gap : ∀ n m : ℤ, m ≠ n → ∀ φ : realTypeSourceSubmodule p,
    displacedRoots (RealDeletedCoeff.complexCLM n (sourcePsiOriginalRootReal hp hp1 n φ):Coeff p) m ∈
      sourcePeriodicSegment hp hp1 φ m
  graph : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c → ∀ φ : realTypeSourceSubmodule p,
    (φ:CoeffPair p) ∈ V → ∀ n : ℤ,
      (φ,sourcePsiOriginalRootReal hp hp1 n φ) ∈ sourcePsiOriginalDeletedOmega V D n

/-- Retain the same source neighborhood while constructing the global solutions. -/
theorem SourceCorollary12_8Data.proposition12_9
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary12_8Data hp hp1 W) (hW : IsOpen W) (hR : realTypeSourceLocus p ⊆ W) :
    SourceProposition12_9Data hp hp1 W :=
  ⟨H,H.previous.previous.previous.previous.existsUnique_originalRealSolution hW hR,
    H.previous.previous.previous.previous.originalRootReal_solution hW hR,
    fun n φ a ha => H.previous.previous.previous.previous.originalRealSolution_unique φ (hR φ.property) n a ha,
    sourcePsiOriginalRootReal_mem_gap hp hp1,
    fun hD φ hφ n => hD.originalRootReal_graph φ hφ n⟩

/-- The original global solution theorem for every finite exponent above one. -/
theorem sourceProposition12_9 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceProposition12_9Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceCorollary12_8 hp hp1
  exact ⟨W,ho,hc,hr,H.proposition12_9 ho hr⟩

end NLS.ZakharovShabat
