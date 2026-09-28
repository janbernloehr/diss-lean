import NLS.ZakharovShabat.SourcePsiGapRootAnalyticReduction

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

end NLS.ZakharovShabat
