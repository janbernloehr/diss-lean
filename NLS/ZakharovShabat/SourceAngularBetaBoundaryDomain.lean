import NLS.ZakharovShabat.SourceAngularBeta
import NLS.ZakharovShabat.SourceBoundaryRootsAnalyticNeighborhood

/-!
# Beta values with analytic moving Dirichlet terminals

Intersect the actual beta construction domain with the common analytic
boundary-coordinate domain. All off-diagonal beta values remain constructed,
and their moving Dirichlet terminals are analytic on the same open source
neighborhood. The full simply connected psi domain is retained separately.
Analyticity of beta itself still requires a parameter-dependent primitive.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All beta values and analytic ordinary boundary coordinates coexist on
one open complex neighborhood of every real source. -/
theorem exists_sourceAngularBeta_common_domain_with_analyticBoundaryRoots
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          (∀ b : BoundaryCondition, ∀ m : ℤ,
            AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
              canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W) ∧
          ∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ,
                b = sourceAngularBeta hp hp1 n m s ψ := by
  obtain ⟨W₀,V,hW₀,hW₀conn,hW₀real,hV,hVreal,hVW₀,s,hs,hbeta⟩ :=
    exists_sourceAngularBeta_common_domain hp hp1
  obtain ⟨A,hA,hAreal,hroots⟩ := exists_sourceBoundaryRoots_analytic_common_domain hp hp1
  refine ⟨W₀,V ∩ A,hW₀,hW₀conn,hW₀real,hV.inter hA,
    (fun φ hφ => ⟨hVreal hφ,hAreal hφ⟩),
    (fun φ hφ => hVW₀ hφ.1),s,hs,?_,?_⟩
  · intro b m ψ hψ
    exact hroots b m ψ hψ.2
  · intro ψ hψ n m hmn
    exact hbeta ψ hψ.1 n m hmn

end NLS.ZakharovShabat
