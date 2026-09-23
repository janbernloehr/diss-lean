import NLS.ComplexAnalysis.HolomorphicCurveHomotopy
import NLS.ZakharovShabat.SourceStandardRootContourAnyCircle

/-!
# Homotopy invariance for inverse standard-root contours

The inverse standard root is analytic away from its closed periodic gap.
Its line integral is constant along a smooth closed-loop homotopy that
stays inside a neighborhood disjoint from that gap.
-/

noncomputable section
open Set
open scoped unitInterval
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The reciprocal standard-root line integral is invariant under a
smooth closed-loop homotopy whose image stays away from its gap. -/
theorem sourceStandardRoot_inv_curveIntegral_eq_of_homotopy
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (φ : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, φ (s, 1) = φ (s, 0))
    {t : Set ℂ}
    (hφt : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, φ (s, u) ∈ t)
    (havoid : closure t ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z =
    ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z := by
  apply NLS.ComplexAnalysis.curveIntegral_eq_of_holomorphic_homotopy
    (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) φ hloop hφt
  · intro z hz
    exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ n z
      (havoid hz)).differentiableAt
  · exact hcontdiff

end NLS.ZakharovShabat
