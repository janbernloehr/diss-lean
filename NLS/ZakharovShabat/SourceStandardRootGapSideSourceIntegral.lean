import NLS.ZakharovShabat.SourceStandardRootGapSideIntegral
import NLS.ZakharovShabat.SourceStandardRootGapSideSourceJoint

/- The canonical periodic source root supplies the boundary values that
   occur in the cosine-parametrized side integral of Lemma 10.4. -/

noncomputable section
open Complex Filter
open scoped Topology

open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual source root approaches its cosine-parametrized upper boundary
    value at every point of the closed gap. -/
theorem sourceStandardRoot_tendsto_gap_upper_cos (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (θ : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Tendsto (sourceStandardRoot hp hp1 ψ n)
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)))
      (𝓝 (-sourceStandardRootHalfGap hp hp1 ψ n * I * (Real.sin θ:ℂ))) := by
  have h := sourceStandardRoot_tendsto_gap_upper_side hp hp1 ψ n
    (Real.cos θ) hgap (Real.cos_mem_Icc θ).1 (Real.cos_mem_Icc θ).2
  have hs : Real.sqrt (1-(Real.cos θ)^2) = Real.sin θ :=
    (Real.sin_eq_sqrt_one_sub_cos_sq hθ0 hθπ).symm
  simpa only [hs] using h

/-- The actual source root approaches its cosine-parametrized lower boundary
    value at every point of the closed gap. -/
theorem sourceStandardRoot_tendsto_gap_lower_cos (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (θ : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Tendsto (sourceStandardRoot hp hp1 ψ n)
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)))
      (𝓝 (sourceStandardRootHalfGap hp hp1 ψ n * I * (Real.sin θ:ℂ))) := by
  have h := sourceStandardRoot_tendsto_gap_lower_side hp hp1 ψ n
    (Real.cos θ) hgap (Real.cos_mem_Icc θ).1 (Real.cos_mem_Icc θ).2
  have hs : Real.sqrt (1-(Real.cos θ)^2) = Real.sin θ :=
    (Real.sin_eq_sqrt_one_sub_cos_sq hθ0 hθπ).symm
  simpa only [hs] using h

/-- Lemma 10.4 for the cosine-parametrized boundary integral of the
    canonical periodic source root: one maximum controls both sides and
    every stopping point. -/
theorem sourceStandardRoot_gapSideBoundaryIntegral_uniform_max_bound
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
      ∀ (t : ℝ) (upper : Bool),
        ‖gapSideBoundaryIntegral
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)
          f t upper / (Real.pi:ℂ)‖ ≤ ‖f z‖ := by
  have hδ : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 := by
    dsimp [sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  exact gapSideBoundaryIntegral_uniform_max_bound _ _ f hδ hf

end NLS.ZakharovShabat
