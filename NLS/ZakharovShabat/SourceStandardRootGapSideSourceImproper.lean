import NLS.ZakharovShabat.SourceStandardRootGapSideImproper
import NLS.ZakharovShabat.SourceStandardRootGapSideSourceIntegral

/- Lemma 10.4 in the canonical periodic gap coordinates, including the
   identification of the path-integral pullback with its improper limit. -/

noncomputable section
open Complex Filter MeasureTheory intervalIntegral
open scoped Topology

open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical source gap satisfies the uniform maximum bound of
    Lemma 10.4 for the explicit weighted side integral. -/
theorem sourceStandardRoot_gapSideWeightedIntegral_uniform_max_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n))) :
    ∃ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n),
      (∀ w ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n), ‖f w‖ ≤ ‖f z‖) ∧
      ∀ (t : ℝ), -1 ≤ t → t ≤ 1 → ∀ (upper : Bool),
        ‖gapSideWeightedIntegral
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)
          f t upper / (Real.pi:ℂ)‖ ≤ ‖f z‖ := by
  have hδ : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 := by
    dsimp [sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  exact gapSideWeightedIntegral_uniform_max_bound _ _ f hδ hf

/-- Lemma 10.4 for the independently defined straight side path integral
    of a canonical source gap. The same attained maximum controls both
    sides and every endpoint `-1 ≤ t ≤ 1`. -/
theorem sourceStandardRoot_gapSidePathIntegral_uniform_max_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n))) :
    ∃ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n),
      (∀ w ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n), ‖f w‖ ≤ ‖f z‖) ∧
      ∀ (t : ℝ), -1 ≤ t → t ≤ 1 → ∀ (upper : Bool),
        ‖gapSidePathIntegral
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)
          f (-1) t upper / (Real.pi:ℂ)‖ ≤ ‖f z‖ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 := by
    dsimp [δ, sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  obtain ⟨z,hz,hmax,hbound⟩ :=
    sourceStandardRoot_gapSideWeightedIntegral_uniform_max_bound hp hp1 ψ n hgap f hf
  refine ⟨z,hz,hmax,?_⟩
  intro t htl htr upper
  change ‖gapSidePathIntegral τ δ f (-1) t upper / (Real.pi:ℂ)‖ ≤ ‖f z‖
  rw [gapSidePathIntegral_eq_boundary τ δ f t hδ htl htr upper,
    ← gapSideWeightedIntegral_eq_boundary τ δ f t hδ htl htr upper]
  exact hbound t htl htr upper

/-- The truncated side path integral converges to its boundary value
    on every canonical noncollapsed gap. -/
theorem sourceStandardRoot_gapSidePathIntegral_tendsto
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n)))
    (t : ℝ) (htl : -1 ≤ t) (htr : t ≤ 1) (upper : Bool) :
    Tendsto (fun ε : ℝ =>
      gapSidePathIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        f (-1+ε) t upper)
      (𝓝[>] (0:ℝ))
      (𝓝 (gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        f t upper)) := by
  have hδ : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 := by
    dsimp [sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  exact gapSidePathIntegral_tendsto_boundary _ _ f hδ hf t htl htr upper

/-- Both-endpoint truncation converges at the right endpoint of a
    canonical noncollapsed gap. -/
theorem sourceStandardRoot_gapSidePathIntegral_double_trunc_tendsto
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n)))
    (upper : Bool) :
    Tendsto (fun ε : ℝ =>
      gapSidePathIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        f (-1+ε) (1-ε) upper)
      (𝓝[>] (0:ℝ))
      (𝓝 (gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        f 1 upper)) := by
  have hδ : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 := by
    dsimp [sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  exact gapSidePathIntegral_double_trunc_tendsto _ _ f hδ hf upper

end NLS.ZakharovShabat
