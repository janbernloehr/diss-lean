import NLS.ZakharovShabat.SourceActionCosineIntegralLimit

/-!
# Weighted horizontal integrals approaching an open real gap

Cosine substitution identifies the ordinary horizontal integral of
the recentered action integrand with the dominated cosine integral.
Thus its upper and lower limits are the corresponding weighted
canonical-root boundary integrals.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted quotient integrated from left to right along a
vertically displaced selected gap. -/
def sourceAction_horizontalIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (q : ℂ) (y : ℝ) : ℂ :=
  ∫ t in (-1:ℝ)..1,
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I
    ((z-q) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) *
      sourceStandardRootHalfGap hp hp1 ψ n

/-- The weighted horizontal integral is the curve integral of the
straight path between the vertically shifted gap endpoints. -/
theorem sourceAction_horizontalSegment_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (q : ℂ) (y : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    (∫ᶜ z in Path.segment (l+(y:ℂ)*I) (r+(y:ℂ)*I),
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (w-q) * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z) =
      sourceAction_horizontalIntegral hp hp1 ψ n q y := by
  exact curveIntegral_sourceGapHorizontalSegment hp hp1 ψ n y _

/-- Cosine substitution converts the weighted horizontal integral to
the integral with an integrable endpoint kernel. -/
theorem sourceAction_horizontalIntegral_eq_cosine
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (q : ℂ) (y : ℝ) :
    sourceAction_horizontalIntegral hp hp1 ψ n q y =
      sourceAction_cosineIntegral hp hp1 ψ n q y := by
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let g : ℝ → ℂ := fun t =>
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I
    ((z-q) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) * δ
  calc
    sourceAction_horizontalIntegral hp hp1 ψ n q y =
        ∫ t in (-1:ℝ)..1, g t := rfl
    _ = ∫ θ in (0:ℝ)..Real.pi,
          (Real.sin θ) • g (Real.cos θ) := by
      simpa only [Real.arccos_one] using
        integral_cos_subst g 1 (by norm_num) (by norm_num)
    _ = sourceAction_cosineIntegral hp hp1 ψ n q y := by
      unfold sourceAction_cosineIntegral
      congr 1
      funext θ
      dsimp [g,δ]
      ring

/-- The upper weighted horizontal integral converges to its
canonical-root boundary integral. -/
theorem sourceAction_horizontalIntegral_tendsto_upper_boundary
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℂ) :
    Tendsto (sourceAction_horizontalIntegral hp hp1 ψ n q)
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (sourceAction_cosineBoundaryIntegral hp hp1 ψ n q true)) := by
  have hfun : sourceAction_horizontalIntegral hp hp1 ψ n q =
      sourceAction_cosineIntegral hp hp1 ψ n q := by
    funext y
    exact sourceAction_horizontalIntegral_eq_cosine hp hp1 ψ n q y
  rw [hfun]
  simpa only [ite_true] using
    (sourceAction_cosineIntegral_tendsto_boundary
      hp hp1 ψ hreal n hopen q true)

/-- The lower weighted horizontal integral converges to its
canonical-root boundary integral. -/
theorem sourceAction_horizontalIntegral_tendsto_lower_boundary
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℂ) :
    Tendsto (sourceAction_horizontalIntegral hp hp1 ψ n q)
      (𝓝[Set.Iio 0] (0:ℝ))
      (𝓝 (sourceAction_cosineBoundaryIntegral hp hp1 ψ n q false)) := by
  have hfun : sourceAction_horizontalIntegral hp hp1 ψ n q =
      sourceAction_cosineIntegral hp hp1 ψ n q := by
    funext y
    exact sourceAction_horizontalIntegral_eq_cosine hp hp1 ψ n q y
  rw [hfun]
  simpa only [Bool.false_eq_true, ite_false] using
    (sourceAction_cosineIntegral_tendsto_boundary
      hp hp1 ψ hreal n hopen q false)

end NLS.ZakharovShabat
