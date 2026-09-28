import NLS.ZakharovShabat.SourcePsiGapRootAnalyticReduction
import NLS.ZakharovShabat.SourcePsiGapRootIsolation
import NLS.ZakharovShabat.SourcePsiDeletedRootFill

/-!
# Global analytic canonical psi roots

For each deleted index, the gap-contained psi solution is globally
defined, pointwise unique, and real analytic on the entire real-type
source Banach space. This combines the existence and uniqueness
construction with the analytic implicit step of Proposition 12.9.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At every finite exponent `p > 1` and deleted index, there is a
unique real-analytic map whose values solve the gap-contained selected
psi equation. The solution predicate includes membership of every
retained root in its assigned periodic gap. -/
theorem existsUnique_analytic_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃! s : realTypeSourceSubmodule p → DeletedCoeff p n,
      AnalyticOnNhd ℝ s univ ∧
      ∀ φ : realTypeSourceSubmodule p,
        SourcePsiGapSolution hp hp1 n (φ : CoeffPair p) (s φ) := by
  refine ⟨sourcePsiGapRoot hp hp1 n,?_,?_⟩
  · exact ⟨analyticOnNhd_sourcePsiGapRoot_real hp hp1 n,
      fun φ => sourcePsiGapRoot_solution hp hp1 n φ⟩
  · intro s hs
    funext φ
    exact SourcePsiGapSolution.eq_sourcePsiGapRoot
      hp hp1 n φ (s φ) (hs.2 φ)

/-- Near each real-type source, the graph of the canonical analytic
solution lies in one open retained-root placement domain. The
isolating discs and the source neighborhood are common to every
nearby real-type source. -/
theorem exists_local_graph_rootPlacement_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ (φ : CoeffPair p) ∈ U ∧
        ∀ ψ : realTypeSourceSubmodule p, (ψ : CoeffPair p) ∈ U →
          (sourcePsiGapRoot hp hp1 n ψ,(ψ : CoeffPair p)) ∈
            sourcePsiRootPlacementDomain hp hp1 (φ : CoeffPair p) N ε n := by
  obtain ⟨N,ε,hε,hεmax,U,hUopen,hφU,hplace⟩ :=
    exists_uniform_rootPlacement_of_gapRoots hp hp1
      (φ : CoeffPair p) φ.property n
  refine ⟨N,ε,hε,hεmax,U,hUopen,hφU,?_⟩
  intro ψ hψ
  exact hplace (ψ : CoeffPair p) hψ
    (sourcePsiGapRoot hp hp1 n ψ)
    (fun m hm => sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hm ψ)

/-- The omitted coordinate can be filled with the periodic midpoint so
that every root of the canonical solution lies in its assigned disc.
One disc family and source neighborhood work for all nearby real-type
potentials. -/
theorem exists_local_graph_filledRootPlacement_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ (φ : CoeffPair p) ∈ U ∧
        ∀ ψ : realTypeSourceSubmodule p, (ψ : CoeffPair p) ∈ U →
          ∃ ξ : ℂ, ξ ∈ sourcePeriodicSegment hp hp1 (ψ : CoeffPair p) n ∧
            ∀ m : ℤ,
              displacedRoots
                (sourcePsiFillDeletedRoot n
                  (sourcePsiGapRoot hp hp1 n ψ) ξ) m ∈
                sourceIsolatingDisc hp hp1 (φ : CoeffPair p) N ε m := by
  obtain ⟨N,ε,hε,hεmax,U,hUopen,_,hφU,hcluster,_⟩ :=
    exists_local_source_connected_isolating_discs hp hp1
      (φ : CoeffPair p) φ.property
  refine ⟨N,ε,hε,hεmax,U,hUopen,hφU,?_⟩
  intro ψ hψ
  refine ⟨sourceStandardRootMidpoint hp hp1 (ψ : CoeffPair p) n,?_,?_⟩
  · simpa only [sourceStandardRootMidpoint] using
      sourcePeriodicMidpoint_mem_segment hp hp1 (ψ : CoeffPair p) n
  intro m
  by_cases hmn : m = n
  · subst m
    rw [displacedRoots_sourcePsiFillDeletedRoot_same]
    exact sourcePeriodicSegment_subset_isolatingDisc
      hp hp1 (φ : CoeffPair p) (ψ : CoeffPair p) N ε n
        (hcluster (ψ : CoeffPair p) hψ n)
        (by simpa only [sourceStandardRootMidpoint] using
          sourcePeriodicMidpoint_mem_segment hp hp1 (ψ : CoeffPair p) n)
  · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
    exact sourcePeriodicSegment_subset_isolatingDisc
      hp hp1 (φ : CoeffPair p) (ψ : CoeffPair p) N ε m
        (hcluster (ψ : CoeffPair p) hψ m)
        (sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hmn ψ)

end NLS.ZakharovShabat
