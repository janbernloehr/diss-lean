import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleMajorants
import NLS.ZakharovShabat.SourceActionContourHomotopy

/-!
# Contour invariance of the normalized-action candidate

The rationalized kernel is holomorphic off the selected periodic
segment, even when that segment collapses. A smooth homotopy between
nested gap-enclosing circles stays inside the outer disc and avoids
the segment. Thus the normalized contour quotient does not depend on
which of those circles is used.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A nested change of valid gap-enclosing circles leaves the
normalized-action contour candidate unchanged, including at a
collapsed selected gap. -/
theorem sourceNormalizedActionCircleCandidate_eq_of_nested_enclosingCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hE : AnalyticOnNhd ℂ
      (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c₁ r₁)) :
    sourceNormalizedActionCircleCandidate hp hp1 n c₀ r₀ ψ =
      sourceNormalizedActionCircleCandidate hp hp1 n c₁ r₁ ψ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let g := (sourcePeriodicGapDisplacement hp hp1 ψ n)^2
  let B := canonicalCriticalGapQuotient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  let f : ℂ → ℂ := fun z => normalizedActionCircleKernel τ g B z * E z
  let H := ContinuousMap.Homotopy.affine
    (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ))
    (NLS.ComplexAnalysis.circlePath c₁ r₁ : C(I, ℂ))
  have hrootfun : normalizedStandardRoot τ g = sourceStandardRoot hp hp1 ψ n := by
    funext z
    simp only [sourceStandardRoot,τ,g,sourceStandardRootMidpoint,
      sourcePeriodicGapDisplacement_apply]
  have hF : ∀ z ∈ range H, AnalyticAt ℂ f z := by
    rintro z ⟨⟨s,u⟩,rfl⟩
    have houter : H (s,u) ∈ closedBall c₁ r₁ :=
      NLS.ComplexAnalysis.affineCircleHomotopy_mem_outer_closedBall
        c₀ c₁ r₀ r₁ hr₀.le hr₁.le hnest s u
    have hnotseg : H (s,u) ∉ sourcePeriodicSegment hp hp1 ψ n := by
      intro hz
      exact (NLS.ComplexAnalysis.affineCircleHomotopy_ne_of_mem_both_balls
        c₀ c₁ _ r₀ r₁ (hseg₀ hz) (hseg₁ hz) s u) rfl
    have hτz : τ ≠ H (s,u) := by
      intro he
      exact hnotseg (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
    have hroot : AnalyticAt ℂ (normalizedStandardRoot τ g) (H (s,u)) := by
      rw [hrootfun]
      exact sourceStandardRoot_analyticAt hp hp1 ψ n _ hnotseg
    have hw : normalizedStandardRoot τ g (H (s,u)) ≠ 0 := by
      rw [hrootfun]
      exact sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n _ hnotseg
    have hplus : τ-H (s,u)+normalizedStandardRoot τ g (H (s,u)) ≠ 0 :=
      normalizedStandardRoot_add_ne_zero τ g _ hτz
    exact (normalizedActionCircleKernel_analyticAt τ g B _ hroot hw hplus).mul
      (hE _ houter)
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  have hInt : (∮ z in C(c₀,r₀), f z) =
      (∮ z in C(c₁,r₁), f z) := by
    have heq :
        (∫ᶜ z in NLS.ComplexAnalysis.circlePath c₀ r₀,
          NLS.ComplexAnalysis.holomorphicOneForm f z) =
        ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₁ r₁,
          NLS.ComplexAnalysis.holomorphicOneForm f z := by
      apply NLS.ComplexAnalysis.curveIntegral_eq_of_holomorphic_homotopy
        f H
        (NLS.ComplexAnalysis.affineHomotopy_loop
          (γ₁ := NLS.ComplexAnalysis.circlePath c₀ r₀)
          (γ₂ := NLS.ComplexAnalysis.circlePath c₁ r₁))
        (t := range H)
      · intro s _ u _
        exact ⟨(s,u),rfl⟩
      · intro z hz
        have hz' : z ∈ range H := by simpa only [hclosed.closure_eq] using hz
        exact (hF z hz').differentiableAt
      · exact NLS.ComplexAnalysis.affineHomotopy_contDiffOn
          (NLS.ComplexAnalysis.circlePath_contDiffOn c₀ r₀)
          (NLS.ComplexAnalysis.circlePath_contDiffOn c₁ r₁)
    calc
      (∮ z in C(c₀,r₀), f z) =
          ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₀ r₀,
            NLS.ComplexAnalysis.holomorphicOneForm f z :=
        (NLS.ComplexAnalysis.curveIntegral_circlePath f c₀ r₀).symm
      _ = ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₁ r₁,
            NLS.ComplexAnalysis.holomorphicOneForm f z := heq
      _ = (∮ z in C(c₁,r₁), f z) :=
        NLS.ComplexAnalysis.curveIntegral_circlePath f c₁ r₁
  have hleft : sourceNormalizedActionCircleCandidate hp hp1 n c₀ r₀ ψ =
      -(Real.pi:ℂ)⁻¹ * (∮ z in C(c₀,r₀), f z) := rfl
  have hright : sourceNormalizedActionCircleCandidate hp hp1 n c₁ r₁ ψ =
      -(Real.pi:ℂ)⁻¹ * (∮ z in C(c₁,r₁), f z) := rfl
  rw [hleft,hright,hInt]

/-- Two possibly nonnested isolating circles give the same normalized
contour quotient when both fit inside a common valid outer disc. -/
theorem sourceNormalizedActionCircleCandidate_eq_of_common_outer
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c₀ c₁ c : ℂ) (r₀ r₁ R : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hR : 0 < R)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₁ r₁)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hnest₀ : closedBall c₀ r₀ ⊆ closedBall c R)
    (hnest₁ : closedBall c₁ r₁ ⊆ closedBall c R)
    (hE : AnalyticOnNhd ℂ
      (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R)) :
    sourceNormalizedActionCircleCandidate hp hp1 n c₀ r₀ ψ =
      sourceNormalizedActionCircleCandidate hp hp1 n c₁ r₁ ψ := by
  calc
    sourceNormalizedActionCircleCandidate hp hp1 n c₀ r₀ ψ =
        sourceNormalizedActionCircleCandidate hp hp1 n c R ψ :=
      sourceNormalizedActionCircleCandidate_eq_of_nested_enclosingCircles
        hp hp1 ψ n c₀ c r₀ R hr₀ hR hseg₀ hseg hnest₀ hE
    _ = sourceNormalizedActionCircleCandidate hp hp1 n c₁ r₁ ψ :=
      (sourceNormalizedActionCircleCandidate_eq_of_nested_enclosingCircles
        hp hp1 ψ n c₁ c r₁ R hr₁ hR hseg₁ hseg hnest₁ hE).symm

end NLS.ZakharovShabat
