import NLS.ZakharovShabat.SourceStandardRootWeightedCosineLimit
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumIntegral

/-!
# Horizontal weighted standard-root integrals approaching a real gap

Cosine substitution turns the straight horizontal contour integral
into the uniformly dominated integral from the previous file. Its
upper and lower limits are exactly the gap-side boundary integrals
of Lemma 10.4.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted selected-root quotient integrated from left to
right along a vertically displaced real gap. -/
def sourceStandardRoot_weighted_horizontalIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (y : ℝ) : ℂ :=
  ∫ t in (-1:ℝ)..1,
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I
    (g z / sourceStandardRoot hp hp1 ψ n z) *
      sourceStandardRootHalfGap hp hp1 ψ n

/-- The weighted horizontal integral equals the curve integral of
the straight path between the shifted gap endpoints. -/
theorem sourceStandardRoot_weighted_horizontalSegment_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (y : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    (∫ᶜ z in Path.segment (l+(y:ℂ)*I) (r+(y:ℂ)*I),
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) =
      sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g y := by
  exact curveIntegral_sourceGapHorizontalSegment hp hp1 ψ n y _

/-- Cosine substitution cancels the horizontal path's signed gap
Jacobian against the change of variables. -/
theorem sourceStandardRoot_weighted_horizontalIntegral_eq_cosine
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (y : ℝ) :
    sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g y =
      sourceStandardRoot_weighted_cosineIntegral hp hp1 ψ n g y := by
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let H : ℝ → ℂ := fun t =>
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I
    (g z / sourceStandardRoot hp hp1 ψ n z) * δ
  calc
    sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g y =
        ∫ t in (-1:ℝ)..1, H t := rfl
    _ = ∫ θ in (0:ℝ)..Real.pi,
          (Real.sin θ) • H (Real.cos θ) := by
      simpa only [Real.arccos_one] using
        integral_cos_subst H 1 (by norm_num) (by norm_num)
    _ = sourceStandardRoot_weighted_cosineIntegral hp hp1 ψ n g y := by
      unfold sourceStandardRoot_weighted_cosineIntegral
      congr 1
      funext θ
      dsimp [H,δ]
      ring

/-- The upper horizontal integral approaches the upper gap-side
boundary integral for a numerator analytic near the closed gap. -/
theorem sourceStandardRoot_weighted_horizontalIntegral_tendsto_upper
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hg : AnalyticOnNhd ℂ g U) :
    Tendsto (sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g)
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true)) := by
  have hfun : sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g =
      sourceStandardRoot_weighted_cosineIntegral hp hp1 ψ n g := by
    funext y
    exact sourceStandardRoot_weighted_horizontalIntegral_eq_cosine
      hp hp1 ψ n g y
  rw [hfun]
  rw [← sourceStandardRoot_weighted_cosineBoundaryIntegral_eq_gapSide]
  simpa only [ite_true] using
    (sourceStandardRoot_weighted_cosineIntegral_tendsto_boundary
      hp hp1 ψ hreal n hopen g U hUopen hgapU hg true)

/-- The lower horizontal integral approaches the lower gap-side
boundary integral. -/
theorem sourceStandardRoot_weighted_horizontalIntegral_tendsto_lower
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hg : AnalyticOnNhd ℂ g U) :
    Tendsto (sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g)
      (𝓝[Set.Iio 0] (0:ℝ))
      (𝓝 (gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) g 1 false)) := by
  have hfun : sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g =
      sourceStandardRoot_weighted_cosineIntegral hp hp1 ψ n g := by
    funext y
    exact sourceStandardRoot_weighted_horizontalIntegral_eq_cosine
      hp hp1 ψ n g y
  rw [hfun]
  rw [← sourceStandardRoot_weighted_cosineBoundaryIntegral_eq_gapSide]
  simpa only [Bool.false_eq_true,ite_false] using
    (sourceStandardRoot_weighted_cosineIntegral_tendsto_boundary
      hp hp1 ψ hreal n hopen g U hUopen hgapU hg false)

end NLS.ZakharovShabat
