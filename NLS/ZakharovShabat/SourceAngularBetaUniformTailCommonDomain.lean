import NLS.ZakharovShabat.SourceAngularBetaAnalyticCommonDomain
import NLS.ZakharovShabat.SourceAngularBetaUniformTailBound

/-!
# A common analytic beta domain with index-uniform tail estimates

The union of quantitative real-centered source neighborhoods retains
all real sources and all analytic beta terms. Each complex source in
that union has a neighborhood on which one constant and selected-index
cutoff work for every off-diagonal pair beyond that cutoff. The estimate
for the remaining finite selected head is still required for Theorem 13.1(i).
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All actual beta terms are analytic on one common complex domain,
and their quantitative tail estimate is locally uniform there in both
indices. Both analytic boundary sequences, unique beta values, and the
original simply connected squared-gap psi extension are retained. -/
theorem exists_sourceAngularBeta_analytic_common_domain_with_uniform_tail_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          (∀ b : BoundaryCondition, ∀ m : ℤ,
            AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W) ∧
          (∀ b : BoundaryCondition, AnalyticOnNhd ℂ (sourceBoundaryDisplacement hp hp1 b) W) ∧
          (∀ ψ ∈ W, ∀ m : ℤ,
            AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
              (periodOnePotential χ) (periodOnePotential_mem χ) m) ψ ∧
            AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
              (periodOnePotential χ) (periodOnePotential_mem χ) m)^2) ψ) ∧
          (∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ, b = sourceAngularBeta hp hp1 n m s ψ) ∧
          (∀ n m : ℤ, m ≠ n → AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) W) ∧
          ∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
            ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ V, ∀ n m : ℤ, K < m.natAbs → m ≠ n →
              ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
                (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
                  ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
                    sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  classical
  obtain ⟨W₀,B,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,s,hs,hroots,hboundary,hsym,hvalues,hbeta⟩ :=
    exists_sourceAngularBeta_analytic_common_domain hp hp1
  have hlocal (φ : realTypeSourceLocus p) := hs.exists_local_uniform_sourceAngularBeta_tail_bound
    B hB hBW₀ hsym φ.val (hBreal φ.property) φ.property
  choose V hV hφV hVB K C hC hbound using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, V φ
  have hW : IsOpen W := isOpen_iUnion hV
  have hWreal : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφV ⟨φ,hφ⟩⟩
  have hWB : W ⊆ B := by
    intro ψ hψ
    obtain ⟨φ,hψV⟩ := mem_iUnion.mp hψ
    exact hVB φ hψV
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWB.trans hBW₀,s,hs,
    (fun b m => (hroots b m).mono hWB),
    (fun b => (hboundary b).mono hWB),
    (fun ψ hψ => hsym ψ (hWB hψ)),
    (fun ψ hψ => hvalues ψ (hWB hψ)),
    (fun n m hmn => (hbeta n m hmn).mono hWB),?_⟩
  intro ψ hψ
  obtain ⟨φ,hψV⟩ := mem_iUnion.mp hψ
  exact ⟨V φ,hV φ,hψV,subset_iUnion V φ,K φ,C φ,hC φ,hbound φ⟩

end NLS.ZakharovShabat
