import NLS.ZakharovShabat.SourceAngularOriginalBetaBound

/-!
# Theorem 13.1(i): beta analyticity and estimate on the retained domain

The unique primitive beta values are analytic throughout the same W and
satisfy the literal estimate locally uniformly in both indices at every
complex source. The earlier path theorem identifies each integrable
admissible endpoint integral with this value. Construction of such paths
at open singular endpoints remains a separate obligation.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The analytic and quantitative beta conclusions retain the original domain and root family. -/
theorem sourceTheorem13_1_original_beta (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
          SourceLemma12_12Data hp hp1 W₀ W s ∧
          (∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n → ∃! b : ℂ, b ∈ sourceAngularBetaValues hp hp1 n m s ψ) ∧
          (∀ n m : ℤ, m ≠ n → AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) W) ∧
          ∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
            ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n m : ℤ, m ≠ n →
              ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
                (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
                  ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
                    sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  obtain ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H⟩ := sourceLemma12_12 hp hp1
  exact ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H,H.beta_original_value_unique,
    H.beta_original_analytic,H.beta_original_uniform_bound⟩

end NLS.ZakharovShabat
