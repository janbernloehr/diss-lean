import NLS.ZakharovShabat.SourceCriticalRootRatioVerticalCircle
import NLS.ComplexAnalysis.NestedCircleHomotopy

/-!
# Contour invariance between nested enclosing circles

The affine homotopy of two circles with nested filled discs remains
inside the outer disc. If both circles enclose the selected gap, every
intermediate circle also encloses it. Thus the critical-root quotient
integrals agree.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Nested circles enclosing the same gap have equal critical-root
quotient integrals when their outer filled disc avoids every other
gap. Their centers need not coincide. -/
theorem circleIntegral_sourceCriticalRootRatio_eq_of_nested_enclosingCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hother : closedBall c₁ r₁ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (∮ z in C(c₀,r₀),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) =
    ∮ z in C(c₁,r₁),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z := by
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let H := ContinuousMap.Homotopy.affine
    (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ))
    (NLS.ComplexAnalysis.circlePath c₁ r₁ : C(I, ℂ))
  have havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨⟨s,u⟩, rfl⟩ m
    by_cases hm : m = n
    · subst m
      intro hz
      exact (NLS.ComplexAnalysis.affineCircleHomotopy_ne_of_mem_both_balls
        c₀ c₁ _ r₀ r₁ (hseg₀ hz) (hseg₁ hz) s u) rfl
    · have hball : H (s,u) ∈ closedBall c₁ r₁ :=
        NLS.ComplexAnalysis.affineCircleHomotopy_mem_outer_closedBall
          c₀ c₁ r₀ r₁ hr₀.le hr₁.le hnest s u
      exact (hother hball) m hm
  have heq := sourceCriticalRootRatio_curveIntegral_eq_of_homotopy_range
    hp hp1 ψ H
    (NLS.ComplexAnalysis.affineHomotopy_loop
      (γ₁ := NLS.ComplexAnalysis.circlePath c₀ r₀)
      (γ₂ := NLS.ComplexAnalysis.circlePath c₁ r₁)) havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₀ r₀)
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₁ r₁))
  calc
    (∮ z in C(c₀,r₀), f z) =
        ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₀ r₀,
          NLS.ComplexAnalysis.holomorphicOneForm f z :=
      (NLS.ComplexAnalysis.curveIntegral_circlePath f c₀ r₀).symm
    _ = ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₁ r₁,
          NLS.ComplexAnalysis.holomorphicOneForm f z := heq
    _ = (∮ z in C(c₁,r₁), f z) :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f c₁ r₁

end NLS.ZakharovShabat
