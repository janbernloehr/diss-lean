import NLS.ZakharovShabat.NormalizedWeightedClosingMap
import NLS.ZakharovShabat.SourceClosingTargets

/-! # Truncated targets in the full weighted source norm -/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual source remainder tends to zero in the full pair norm. -/
theorem tendsto_normalizedWeightedSourceRemainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) :
    Tendsto (fun N : ℕ => normalizedWeightedSourceRemainder hp w φ N) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₀,_,U,_,_,hφ,_,hR⟩ := exists_uniform_analytic_weightedResonantCenterRemainder
    hp hp1 w (normalizedWeightedPeriodOne w φ) ε hε
  refine ⟨N₀,fun N hN => ?_⟩
  simpa only [dist_zero_right,norm_normalizedWeightedSourceRemainder] using
    ((hR N hN).2 (normalizedWeightedPeriodOne w φ) hφ).2

/-- At each fixed source, the actual adapted maps converge to the identity. -/
theorem tendsto_normalizedWeightedClosingMap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) :
    Tendsto (fun N : ℕ => normalizedWeightedClosingMap hp w φ N) atTop (𝓝 φ) := by
  simpa only [normalizedWeightedClosingMap,add_zero] using
    tendsto_const_nhds.add (tendsto_normalizedWeightedSourceRemainder hp hp1 w φ)

/-- Truncation error and the actual spectral remainder jointly tend to zero. -/
theorem tendsto_normalizedWeightedClosingTarget_difference
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) :
    Tendsto (fun N : ℕ => sourceSymmetricTruncate N φ-normalizedWeightedClosingMap hp w φ (N+1))
      atTop (𝓝 0) := by
  have hF := (tendsto_normalizedWeightedClosingMap hp hp1 w φ).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,sub_self] using (tendsto_sourceSymmetricTruncate hp φ).sub hF

/-- A common positive inverse image radius eventually contains the actual
truncated targets, although its center depends on the cutoff. -/
theorem eventually_normalizedWeightedClosingTarget_mem_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      sourceSymmetricTruncate N φ ∈ ball (normalizedWeightedClosingMap hp w φ (N+1)) δ := by
  have h := (tendsto_normalizedWeightedClosingTarget_difference hp hp1 w φ).eventually (ball_mem_nhds 0 hδ)
  simpa only [mem_ball,dist_eq_norm,sub_zero] using h

end NLS.ZakharovShabat
