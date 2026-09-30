import NLS.ZakharovShabat.SourceAngularCauchySheetPrimitive

/-!
# Actual beta analyticity through collapsed real gaps

The interior Cauchy solution constructs normalized primitives on the
actual Dirichlet sheet. Its terminal value is therefore the actual beta,
through both regular and endpoint terminals on the whole source chart.
The analytic candidate proves source analyticity at every real base,
without a nonzero-gap condition.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- At a regular terminal the Cauchy construction is an actual normalized
Dirichlet primitive, so its terminal value equals beta. -/
theorem betaCauchyCandidate_eq_beta_of_regular
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (hw : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0) :
    sourceAngularBetaCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ ψ =
      sourceAngularBeta hp hp1 n m s ψ := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  let H : ℂ → ℂ := fun z => sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ (z,ψ)
  let F : ℂ → ℂ := fun z => sourceStandardRoot hp hp1 ψ m z*H z
  let E : ℂ → ℂ := fun z => sourceAngularRootSheet hp w (z,ψ) /
    (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z)*H z
  have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
  have hE : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ (c m) r F 0 E :=
    ⟨D.gap_enclosed ψ hψ,hw,D.cauchy_sheet_primitive_data ψ hψ n hmn ρ hrρ hρR w hw,
      ⟨D.terminal_enclosed ψ hψ,hbase.1⟩,hbase.2⟩
  have hvalue : E μ = sourceAngularBetaCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ ψ := by
    dsimp only [E,sourceAngularBetaCauchyCandidate]
    rw [hbase.2]
  exact hvalue.symm.trans hE.beta_eq_terminal.symm

/-- The exact formula holds on the whole source chart, including nearby
complex sources and both periodic Dirichlet endpoint conventions. -/
theorem betaCauchyCandidate_eq_beta
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) :
    sourceAngularBetaCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ ψ =
      sourceAngularBeta hp hp1 n m s ψ := by
  by_cases hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m
  · exact D.betaCauchyCandidate_eq_beta_of_endpoint ψ hψ n ρ hend
  · apply D.betaCauchyCandidate_eq_beta_of_regular ψ hψ n hmn ρ hrρ hρR
    exact sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain hp hp1 ψ m
      (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
        (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m)))
      (fun h => hend (Or.inl h)) (fun h => hend (Or.inr h))

/-- Only analyticity of the actual moving Dirichlet terminal is needed;
individual periodic endpoints and the gap need not be analytic. -/
theorem analyticAt_beta
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (n : ℤ) (hmn : m ≠ n) (φ : CoeffPair p) (hφ : φ ∈ V)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ) :
    AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ := by
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have heq : sourceAngularBetaCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ =ᶠ[𝓝 φ]
      sourceAngularBeta hp hp1 n m s := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    exact D.betaCauchyCandidate_eq_beta ψ hψ n hmn ρ hrρ hρR
  exact (D.analyticAt_betaCauchyCandidate n ρ hrρ hρR φ hφ hμ).congr heq

/-- On a chart with an analytic moving terminal, every off-diagonal beta
term is analytic throughout the complex source neighborhood. -/
theorem analyticOnNhd_beta
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (n : ℤ) (hmn : m ≠ n)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) V) :
    AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) V :=
  fun ψ hψ => D.analyticAt_beta n hmn ψ hψ (hμ ψ hψ)

/-- Every real base source has analytic off-diagonal beta, including a
collapsed selected gap and either periodic Dirichlet terminal. -/
theorem analyticAt_beta_of_realSource
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (hmn : m ≠ n) : AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ :=
  D.analyticAt_beta n hmn φ hφ
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ hreal m)

end SourceAngularJointAnnulusChartData

/-- The actual common beta domains retain both analytic boundary
sequences, all unique beta values, and the simply connected psi extension.
At every real source all off-diagonal beta terms are analytic, including
central indices and collapsed gaps. -/
theorem exists_sourceAngularBeta_common_domain_with_realSourceAnalyticity
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          (∀ b : BoundaryCondition, ∀ m : ℤ,
            AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W) ∧
          (∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ, b = sourceAngularBeta hp hp1 n m s ψ) ∧
          (∀ φ : realTypeSourceLocus p, ∀ n m : ℤ, m ≠ n →
            AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ.val) ∧
          ∀ φ : realTypeSourceLocus p, ∀ m : ℤ,
            ∃ V : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
              ∃ r R : ℝ, ∃ z₀ : ℂ, φ.val ∈ V ∧
                SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀ ∧
                  ∀ n : ℤ, m ≠ n → AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) V := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hbeta,_,hcharts⟩ :=
    exists_sourceAngularBeta_common_domain_with_jointAnnularPrimitives hp hp1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hbeta,?_,?_⟩
  · intro φ n m hmn
    obtain ⟨V,c,T,r,R,z₀,hφ,D⟩ := hcharts φ m
    exact D.analyticAt_beta_of_realSource φ.val hφ φ.property n hmn
  · intro φ m
    obtain ⟨V,c,T,r,R,z₀,hφ,D⟩ := hcharts φ m
    exact ⟨V,c,T,r,R,z₀,hφ,D,fun n hmn => D.analyticOnNhd_beta n hmn
      ((hroots .dirichlet m).mono D.source_subset)⟩

end NLS.ZakharovShabat
