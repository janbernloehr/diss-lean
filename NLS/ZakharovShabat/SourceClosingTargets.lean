import NLS.ZakharovShabat.SourceAdaptedClosingMap
import NLS.ZakharovShabat.SourceRealTypeFiniteApproximation

/-!
# Truncated targets for the actual source closing map

The adapted map at a fixed source converges to that source as the
cutoff grows. Symmetric Fourier truncations therefore eventually lie
in every fixed positive image ball. A truncation at radius `N` has
zero target coefficients at every resonance with `N+1 ≤ |n|`.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both target components vanish beyond the retained symmetric block. -/
theorem sourceSymmetricTruncate_high (N : ℕ) (φ : CoeffPair p) (n : ℤ)
    (hn : N+1 ≤ n.natAbs) :
    (sourceSymmetricTruncate N φ).fst (-n) = 0 ∧
      (sourceSymmetricTruncate N φ).snd n = 0 := by
  have hn' : n ∉ Finset.Icc (-(N : ℤ)) N := by
    simp only [Finset.mem_Icc]
    omega
  have hm' : -n ∉ Finset.Icc (-(N : ℤ)) N := by
    simp only [Finset.mem_Icc]
    omega
  exact ⟨by change Coeff.truncate _ φ.fst (-n) = 0; simp [hm'],
    by change Coeff.truncate _ φ.snd n = 0; simp [hn']⟩

/-- The actual source remainder tends to zero in the full pair norm. -/
theorem tendsto_sourceResonantCenterRemainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Tendsto (fun N : ℕ => sourceResonantCenterRemainder hp φ N) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₀,_,U,_,_,hφ,_,hR⟩ := exists_uniform_analytic_weightedResonantCenterRemainder
    hp hp1 SpectralWeight.one (sourceWeightedPeriodOne φ) ε hε
  refine ⟨N₀,fun N hN => ?_⟩
  simpa only [dist_zero_right,norm_sourceResonantCenterRemainder] using
    ((hR N hN).2 (sourceWeightedPeriodOne φ) hφ).2

/-- At each fixed source, the actual adapted maps converge to the identity. -/
theorem tendsto_sourceAdaptedClosingMap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Tendsto (fun N : ℕ => sourceAdaptedClosingMap hp φ N) atTop (𝓝 φ) := by
  simpa only [sourceAdaptedClosingMap,add_zero] using
    tendsto_const_nhds.add (tendsto_sourceResonantCenterRemainder hp hp1 φ)

/-- Truncation error and the actual spectral remainder jointly tend to zero. -/
theorem tendsto_sourceClosingTarget_difference
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Tendsto (fun N : ℕ => sourceSymmetricTruncate N φ-sourceAdaptedClosingMap hp φ (N+1))
      atTop (𝓝 0) := by
  have hF := (tendsto_sourceAdaptedClosingMap hp hp1 φ).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,sub_self] using (tendsto_sourceSymmetricTruncate hp φ).sub hF

/-- A common positive inverse image radius eventually contains the actual
truncated targets, although its center depends on the cutoff. -/
theorem eventually_sourceClosingTarget_mem_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      sourceSymmetricTruncate N φ ∈ ball (sourceAdaptedClosingMap hp φ (N+1)) δ := by
  have h := (tendsto_sourceClosingTarget_difference hp hp1 φ).eventually (ball_mem_nhds 0 hδ)
  simpa only [mem_ball,dist_eq_norm,sub_zero] using h

end NLS.ZakharovShabat
