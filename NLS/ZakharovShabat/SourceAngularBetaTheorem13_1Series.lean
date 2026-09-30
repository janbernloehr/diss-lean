import NLS.ZakharovShabat.SourceAngularBetaSeriesAnalytic
import NLS.ZakharovShabat.SourceAngularBetaDecay

/-!
# Theorem 13.1(i) and (iii): the actual analytic beta correction

On one common complex neighborhood of the entire real source locus,
every actual beta term satisfies the locally uniform reciprocal index
estimate, and its actual correction series converges absolutely and
locally uniformly to an analytic function. At each source the complete
absolute sum, and hence the correction, tends to zero as `|n|` tends to
infinity. The full normalized psi extension and boundary data are retained.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complete series assertion of Theorem 13.1(iii), with the
stronger vanishing of the complete absolute sum at every source. -/
structure SourceAngularBetaSeriesData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) : Prop
    extends SourceAngularBetaSeriesAnalyticData hp hp1 W s where
  absolute_decay : ∀ ψ ∈ W,
    Tendsto (fun n : ℤ => ∑' m : ℤ, ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖)
      cofinite (𝓝 0)
  correction_decay : ∀ ψ ∈ W,
    Tendsto (fun n : ℤ => sourceAngularBetaCorrection hp hp1 n s ψ) cofinite (𝓝 0)

/-- Add the index decay to the analytic series on its existing
domain, using the locally uniform all-index beta estimate. -/
theorem SourceAngularBetaSeriesAnalyticData.with_decay_of_uniform_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (D : SourceAngularBetaSeriesAnalyticData hp hp1 W s)
    (hbound : ∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n m : ℤ, m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)|) :
    SourceAngularBetaSeriesData hp hp1 W s := by
  have hdecay (ψ : CoeffPair p) (hψ : ψ ∈ W) :
      Tendsto (fun n : ℤ => ∑' m : ℤ, ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖)
          cofinite (𝓝 0) ∧
        Tendsto (fun n : ℤ => sourceAngularBetaCorrection hp hp1 n s ψ) cofinite (𝓝 0) := by
    obtain ⟨U,_,hψU,_,C,hC,hest⟩ := hbound ψ hψ
    exact sourceAngularBetaCorrection_decay_of_bound hp hp1 s ψ C hC.le (hest ψ hψU)
  exact ⟨D,fun ψ hψ => (hdecay ψ hψ).1,fun ψ hψ => (hdecay ψ hψ).2⟩

/-- The full individual-term and correction-series assertions of
Theorem 13.1(i) and (iii) hold on one common open complex neighborhood
of all real sources, with all normalized psi and boundary data retained. -/
theorem exists_sourceAngularBeta_theorem13_1_i_iii
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
          SourceAngularBetaSeriesData hp hp1 W s := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hboundary,hsym,hvalues,hbeta,hbound,D⟩ :=
    exists_sourceAngularBetaSeries_analytic_common_domain hp hp1
  exact ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hboundary,hsym,hvalues,hbeta,hbound,
    D.with_decay_of_uniform_bound hbound⟩

end NLS.ZakharovShabat
