import NLS.ZakharovShabat.SourceComplexActionGradient
import NLS.ZakharovShabat.SourceActionContourHomotopy
import NLS.ComplexAnalysis.CircleCurveIntegral

/-!
# Contour invariance of the action gradient

The discriminant-variation quotient is analytic off all periodic
cuts, so its contour integral is invariant under smooth
cut-avoiding homotopies. In particular, nested circles enclosing the
same selected gap give the same gradient value.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A smooth closed-loop homotopy avoiding every periodic cut
preserves the discriminant-variation contour integral. -/
theorem sourceActionGradient_curveIntegral_eq_of_homotopy_range
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ h : CoeffPair p)
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w =>
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
          sourceCanonicalRoot hp hp1 φ w) z) =
      ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w =>
          (fderiv ℂ (fun ψ : CoeffPair p =>
            canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
            sourceCanonicalRoot hp hp1 φ w) z := by
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  apply NLS.ComplexAnalysis.curveIntegral_eq_of_holomorphic_homotopy
    (fun w =>
      (fderiv ℂ (fun ψ : CoeffPair p =>
        canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
        sourceCanonicalRoot hp hp1 φ w)
    H hloop (t := range H)
  · intro s _ u _
    exact ⟨(s,u),rfl⟩
  · intro z hz
    have hz' : z ∈ range H := by
      simpa only [hclosed.closure_eq] using hz
    exact ((analyticOnNhd_sourceDiscriminantVariation_div_root
      hp hp1 φ h) z (havoid hz')).differentiableAt
  · exact hcontdiff

/-- The gradient contour integral is unchanged by a smooth
cut-avoiding homotopy between two positively oriented circles. -/
theorem sourceActionGradient_circleIntegral_eq_of_homotopy_range
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ h : CoeffPair p)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (H : (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ)).Homotopy
      (NLS.ComplexAnalysis.circlePath c₁ r₁))
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    (∮ z in C(c₀,r₀),
      (fderiv ℂ (fun ψ : CoeffPair p =>
        canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
        sourceCanonicalRoot hp hp1 φ z) =
      ∮ z in C(c₁,r₁),
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z := by
  let f : ℂ → ℂ := fun w =>
    (fderiv ℂ (fun ψ : CoeffPair p =>
      canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
      sourceCanonicalRoot hp hp1 φ w
  have heq := sourceActionGradient_curveIntegral_eq_of_homotopy_range
    hp hp1 φ h H hloop havoid hcontdiff
  calc
    (∮ z in C(c₀,r₀), f z) =
        ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₀ r₀,
          NLS.ComplexAnalysis.holomorphicOneForm f z :=
      (NLS.ComplexAnalysis.curveIntegral_circlePath f c₀ r₀).symm
    _ = ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₁ r₁,
          NLS.ComplexAnalysis.holomorphicOneForm f z := heq
    _ = (∮ z in C(c₁,r₁), f z) :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f c₁ r₁

/-- Nested circles enclosing the same selected gap give equal
gradient integrals when the outer disc avoids all other gaps. -/
theorem sourceActionGradient_circleIntegral_eq_of_nested_enclosingCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ h : CoeffPair p) (n : ℤ)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 φ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 φ n ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hother : closedBall c₁ r₁ ⊆
      sourceStandardRootOmittedDomain hp hp1 φ n) :
    (∮ z in C(c₀,r₀),
      (fderiv ℂ (fun ψ : CoeffPair p =>
        canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
        sourceCanonicalRoot hp hp1 φ z) =
      ∮ z in C(c₁,r₁),
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z := by
  let H := ContinuousMap.Homotopy.affine
    (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ))
    (NLS.ComplexAnalysis.circlePath c₁ r₁ : C(I, ℂ))
  have havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 φ := by
    rintro z ⟨⟨s,u⟩,rfl⟩ m
    by_cases hm : m = n
    · subst m
      intro hz
      exact (NLS.ComplexAnalysis.affineCircleHomotopy_ne_of_mem_both_balls
        c₀ c₁ _ r₀ r₁ (hseg₀ hz) (hseg₁ hz) s u) rfl
    · have hball : H (s,u) ∈ closedBall c₁ r₁ :=
        NLS.ComplexAnalysis.affineCircleHomotopy_mem_outer_closedBall
          c₀ c₁ r₀ r₁ hr₀.le hr₁.le hnest s u
      exact (hother hball) m hm
  exact sourceActionGradient_circleIntegral_eq_of_homotopy_range
    hp hp1 φ h c₀ c₁ r₀ r₁ H
    (NLS.ComplexAnalysis.affineHomotopy_loop
      (γ₁ := NLS.ComplexAnalysis.circlePath c₀ r₀)
      (γ₂ := NLS.ComplexAnalysis.circlePath c₁ r₁))
    havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₀ r₀)
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₁ r₁))

/-- Two possibly nonnested isolating circles give the same gradient
integral when both lie inside a common larger isolating circle. -/
theorem sourceActionGradient_circleIntegral_eq_of_common_outer
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ h : CoeffPair p) (n : ℤ)
    (c₀ c₁ c : ℂ) (r₀ r₁ R : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hR : 0 < R)
    (hseg₀ : sourcePeriodicSegment hp hp1 φ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 φ n ⊆ ball c₁ r₁)
    (hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R)
    (hnest₀ : closedBall c₀ r₀ ⊆ closedBall c R)
    (hnest₁ : closedBall c₁ r₁ ⊆ closedBall c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 φ n) :
    (∮ z in C(c₀,r₀),
      (fderiv ℂ (fun ψ : CoeffPair p =>
        canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
        sourceCanonicalRoot hp hp1 φ z) =
      ∮ z in C(c₁,r₁),
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z := by
  calc
    (∮ z in C(c₀,r₀),
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z) =
        ∮ z in C(c,R),
          (fderiv ℂ (fun ψ : CoeffPair p =>
            canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
            sourceCanonicalRoot hp hp1 φ z :=
      sourceActionGradient_circleIntegral_eq_of_nested_enclosingCircles
        hp hp1 φ h n c₀ c r₀ R hr₀ hR hseg₀ hseg hnest₀ hother
    _ = (∮ z in C(c₁,r₁),
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z) :=
      (sourceActionGradient_circleIntegral_eq_of_nested_enclosingCircles
        hp hp1 φ h n c₁ c r₁ R hr₁ hR hseg₁ hseg hnest₁ hother).symm

end NLS.ZakharovShabat
