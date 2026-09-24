import NLS.ZakharovShabat.SourceCriticalRootRatioCosineBoundaryZero

/-!
# Horizontal integrals approaching a real periodic gap

The cosine parametrization used to dominate the boundary singularity
is the ordinary straight horizontal integral after substitution. This
transfers the zero limits to the two displaced horizontal segments
needed for a shrinking contour around the gap.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The critical-root quotient integrated from the left to the right
endpoint of a selected gap, shifted vertically by y. -/
def sourceCriticalRootRatio_horizontalIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (y : ℝ) : ℂ :=
  ∫ r in (-1:ℝ)..1,
    (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n r + (y:ℂ)*I) /
      sourceCanonicalRoot hp hp1 ψ
        (sourceCanonicalRootGapPoint hp hp1 ψ n r + (y:ℂ)*I)) *
      sourceStandardRootHalfGap hp hp1 ψ n

/-- The cosine integral is exactly the horizontal integral for every
vertical displacement, including zero as a formal identity. -/
theorem sourceCriticalRootRatio_horizontalIntegral_eq_cosine
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (y : ℝ) :
    sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y =
      ∫ θ in (0:ℝ)..Real.pi,
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I) /
          sourceCanonicalRoot hp hp1 ψ
            (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I)) *
          (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ)) := by
  let g : ℝ → ℂ := fun r =>
    (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n r + (y:ℂ)*I) /
      sourceCanonicalRoot hp hp1 ψ
        (sourceCanonicalRootGapPoint hp hp1 ψ n r + (y:ℂ)*I)) *
      sourceStandardRootHalfGap hp hp1 ψ n
  calc
    sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y =
        ∫ r in (-1:ℝ)..1, g r := rfl
    _ = ∫ θ in (0:ℝ)..Real.pi,
          (Real.sin θ) • g (Real.cos θ) := by
      simpa only [Real.arccos_one] using
        integral_cos_subst g 1 (by norm_num) (by norm_num)
    _ = _ := by
      congr 1
      funext θ
      dsimp [g]
      ring

/-- The upper horizontal integral tends to zero as its height tends
to zero from above. -/
theorem sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_upper
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    Tendsto (sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
  change Tendsto (fun y : ℝ =>
    sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y)
    (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0)
  simpa only [sourceCriticalRootRatio_horizontalIntegral_eq_cosine] using
    sourceCriticalRootRatio_upper_cosineIntegral_tendsto_zero
      hp hp1 ψ hreal n hopen

/-- The lower horizontal integral tends to zero as its height tends
to zero from below. -/
theorem sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_lower
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    Tendsto (sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n)
      (𝓝[Set.Iio 0] (0:ℝ)) (𝓝 0) := by
  change Tendsto (fun y : ℝ =>
    sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y)
    (𝓝[Set.Iio 0] (0:ℝ)) (𝓝 0)
  simpa only [sourceCriticalRootRatio_horizontalIntegral_eq_cosine] using
    sourceCriticalRootRatio_lower_cosineIntegral_tendsto_zero
      hp hp1 ψ hreal n hopen

end NLS.ZakharovShabat
