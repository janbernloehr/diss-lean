import NLS.ZakharovShabat.SourceAngularBetaSeries
import NLS.ComplexAnalysis.LocalAnalyticApproximationOn
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-!
# The analytic sum of the actual off-diagonal beta series

Symmetric partial sums are analytic on the original common angular
domain. Local uniform convergence and the Banach-space holomorphic
limit theorem make their actual sum analytic, including collapsed gaps
and endpoint terminals. The decay assertion in Theorem 13.1(iii) is
treated separately.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Absolute convergence, local uniform convergence, and analyticity
of Section 13's actual correction series on one common domain. -/
structure SourceAngularBetaSeriesAnalyticData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) : Prop where
  summable_norm : ∀ ψ ∈ W, ∀ n : ℤ,
    Summable (fun m => ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖)
  locally_uniform : ∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧ ∀ n : ℤ,
    TendstoUniformlyOn
      (fun (N : ℕ) ψ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        sourceAngularBetaSeriesTerm hp hp1 n s ψ m)
      (sourceAngularBetaCorrection hp hp1 n s) atTop V
  analytic_correction : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 n s) W

/-- Local uniform convergence of the actual analytic beta terms
implies analyticity of their sum in the full Banach source variable. -/
theorem analyticOnNhd_sourceAngularBetaCorrection_of_locally_uniform
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (W : Set (CoeffPair p)) (hW : IsOpen W)
    (hbeta : ∀ n m : ℤ, m ≠ n → AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) W)
    (huniform : ∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∀ n : ℤ,
      TendstoUniformlyOn
        (fun (N : ℕ) ψ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
          sourceAngularBetaSeriesTerm hp hp1 n s ψ m)
        (sourceAngularBetaCorrection hp hp1 n s) atTop V)
    (n : ℤ) : AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 n s) W := by
  classical
  have hsum (N : ℕ) : AnalyticOnNhd ℂ
      (fun ψ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        sourceAngularBetaSeriesTerm hp hp1 n s ψ m) W := by
    intro ψ hψ
    apply Finset.analyticAt_fun_sum
    intro m _
    by_cases hmn : m = n
    · simp only [sourceAngularBetaSeriesTerm, if_pos hmn]
      exact analyticAt_const
    · simp only [sourceAngularBetaSeriesTerm, if_neg hmn]
      exact hbeta n m hmn ψ hψ
  have happrox := HasLocalUniformAnalyticApproximationOn.of_open_local_uniform hW hsum
    (fun φ hφ => by
      obtain ⟨V,hV,hφV,hconv⟩ := huniform φ hφ
      exact ⟨V,hV,hφV,hconv n⟩)
  exact analyticOnNhd_of_complexSmoothOn _ hW happrox.contDiffOn

/-- The complete assertion of 13.1(i) supplies absolute and locally
uniform convergence, and hence analyticity, of the actual beta series. -/
theorem sourceAngularBetaSeriesAnalyticData_of_uniform_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (W : Set (CoeffPair p)) (hW : IsOpen W)
    (hboundary : AnalyticOnNhd ℂ (sourceBoundaryDisplacement hp hp1 .dirichlet) W)
    (hbeta : ∀ n m : ℤ, m ≠ n → AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) W)
    (hbound : ∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n m : ℤ, m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)|) :
    SourceAngularBetaSeriesAnalyticData hp hp1 W s := by
  have hsum : ∀ ψ ∈ W, ∀ n : ℤ,
      Summable (fun m => ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖) := by
    intro ψ hψ n
    obtain ⟨U,_,hψU,_,C,hC,hest⟩ := hbound ψ hψ
    exact (summable_norm_sourceAngularBetaSeriesTerm_of_bound hp hp1 n s ψ C hC.le
      (hest ψ hψU n)).1
  have huniform : ∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧ ∀ n : ℤ,
      TendstoUniformlyOn
        (fun (N : ℕ) ψ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
          sourceAngularBetaSeriesTerm hp hp1 n s ψ m)
        (sourceAngularBetaCorrection hp hp1 n s) atTop V := by
    intro φ hφ
    obtain ⟨U,hU,hφU,hUW,C,hC,hest⟩ := hbound φ hφ
    obtain ⟨V,hV,hφV,hVU,hconv⟩ := exists_local_uniform_sourceAngularBetaSeries_of_bound
      hp hp1 s U hU φ hφU (hboundary φ hφ) C hC.le hest
    exact ⟨V,hV,hφV,hVU.trans hUW,hconv⟩
  exact ⟨hsum,huniform,analyticOnNhd_sourceAngularBetaCorrection_of_locally_uniform hp hp1 s W hW
    hbeta (fun φ hφ => by
      obtain ⟨V,hV,hφV,_,hconv⟩ := huniform φ hφ
      exact ⟨V,hV,hφV,hconv⟩)⟩

/-- The actual beta correction series is absolutely and locally
uniformly convergent and analytic on the same common domain as all
individual beta terms. All normalized psi and boundary data are retained. -/
theorem exists_sourceAngularBetaSeries_analytic_common_domain
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
          (∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
            ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ V, ∀ n m : ℤ, m ≠ n →
              ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
                (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
                  ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
                    sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)|) ∧
          SourceAngularBetaSeriesAnalyticData hp hp1 W s := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hboundary,hsym,hvalues,hbeta,hbound⟩ :=
    exists_sourceAngularBeta_theorem13_1_i hp hp1
  exact ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hboundary,hsym,hvalues,hbeta,hbound,
    sourceAngularBetaSeriesAnalyticData_of_uniform_bound hp hp1 s W hW (hboundary .dirichlet)
      hbeta hbound⟩

end NLS.ZakharovShabat
