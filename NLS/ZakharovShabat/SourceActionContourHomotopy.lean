import NLS.ZakharovShabat.SourceActionCircle
import NLS.ComplexAnalysis.NestedCircleHomotopy

/-!
# Contour invariance of the source action

The action integrand is the spectral parameter times the
critical-root quotient. It remains holomorphic off the periodic
cuts. Smooth homotopies in that domain therefore preserve its curve
integral. In particular, two nested isolating circles determine the
same action even when their centers differ.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A smooth closed-loop homotopy avoiding every periodic cut
preserves the weighted critical-root quotient integral. -/
theorem sourceAction_curveIntegral_eq_of_homotopy_range
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => w * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z) =
      ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => w * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z := by
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  apply NLS.ComplexAnalysis.curveIntegral_eq_of_holomorphic_homotopy
    (fun w => w * sourceCriticalRootRatioJoint hp hp1 (w,ψ))
    H hloop (t := range H)
  · intro s _ u _
    exact ⟨(s,u),rfl⟩
  · intro z hz
    have hz' : z ∈ range H := by simpa only [hclosed.closure_eq] using hz
    exact (analyticAt_id.mul
      (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
        (havoid hz'))).differentiableAt
  · exact hcontdiff

/-- The source action is unchanged by a smooth homotopy between two
positively oriented circles, provided the homotopy avoids every cut. -/
theorem sourceActionCircle_eq_of_homotopy_range
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (H : (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ)).Homotopy
      (NLS.ComplexAnalysis.circlePath c₁ r₁))
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    sourceActionCircle hp hp1 ψ c₀ r₀ =
      sourceActionCircle hp hp1 ψ c₁ r₁ := by
  let f : ℂ → ℂ := fun w => w * sourceCriticalRootRatioJoint hp hp1 (w,ψ)
  have heq := sourceAction_curveIntegral_eq_of_homotopy_range
    hp hp1 ψ H hloop havoid hcontdiff
  have hcircle : (∮ z in C(c₀,r₀), f z) =
      ∮ z in C(c₁,r₁), f z := by
    calc
      (∮ z in C(c₀,r₀), f z) =
          ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₀ r₀,
            NLS.ComplexAnalysis.holomorphicOneForm f z :=
        (NLS.ComplexAnalysis.curveIntegral_circlePath f c₀ r₀).symm
      _ = ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₁ r₁,
            NLS.ComplexAnalysis.holomorphicOneForm f z := heq
      _ = (∮ z in C(c₁,r₁), f z) :=
        NLS.ComplexAnalysis.curveIntegral_circlePath f c₁ r₁
  exact congrArg ((Real.pi : ℂ)⁻¹ * ·) hcircle

/-- Nested circles enclosing the same selected gap give equal
actions when the outer filled disc avoids every other gap. -/
theorem sourceActionCircle_eq_of_nested_enclosingCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hother : closedBall c₁ r₁ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceActionCircle hp hp1 ψ c₀ r₀ =
      sourceActionCircle hp hp1 ψ c₁ r₁ := by
  let H := ContinuousMap.Homotopy.affine
    (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ))
    (NLS.ComplexAnalysis.circlePath c₁ r₁ : C(I, ℂ))
  have havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
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
  exact sourceActionCircle_eq_of_homotopy_range
    hp hp1 ψ c₀ c₁ r₀ r₁ H
    (NLS.ComplexAnalysis.affineHomotopy_loop
      (γ₁ := NLS.ComplexAnalysis.circlePath c₀ r₀)
      (γ₂ := NLS.ComplexAnalysis.circlePath c₁ r₁))
    havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₀ r₀)
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₁ r₁))

/-- Two possibly nonnested isolating circles have the same action
when both fit inside a common larger isolating circle. -/
theorem sourceActionCircle_eq_of_common_outer
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c₀ c₁ c : ℂ) (r₀ r₁ R : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hR : 0 < R)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₁ r₁)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hnest₀ : closedBall c₀ r₀ ⊆ closedBall c R)
    (hnest₁ : closedBall c₁ r₁ ⊆ closedBall c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceActionCircle hp hp1 ψ c₀ r₀ =
      sourceActionCircle hp hp1 ψ c₁ r₁ := by
  calc
    sourceActionCircle hp hp1 ψ c₀ r₀ =
        sourceActionCircle hp hp1 ψ c R :=
      sourceActionCircle_eq_of_nested_enclosingCircles hp hp1 ψ n
        c₀ c r₀ R hr₀ hR hseg₀ hseg hnest₀ hother
    _ = sourceActionCircle hp hp1 ψ c₁ r₁ :=
      (sourceActionCircle_eq_of_nested_enclosingCircles hp hp1 ψ n
        c₁ c r₁ R hr₁ hR hseg₁ hseg hnest₁ hother).symm

/-- Near a real-type base source, one fixed outer circle defines the
same action as every smaller isolating circle inside it, uniformly
over the nearby complex source neighborhood. -/
theorem exists_local_sourceActionCircle_eq_of_inner_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        (∀ ψ ∈ V, ∀ c₀ : ℂ, ∀ r₀ : ℝ, 0 < r₀ →
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀ →
          closedBall c₀ r₀ ⊆ closedBall c R →
            sourceActionCircle hp hp1 ψ c₀ r₀ =
              sourceActionCircle hp hp1 ψ c R) := by
  obtain ⟨V,hVopen,hφV,c,R,hR,hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle
      hp hp1 φ hφ n
  refine ⟨V,hVopen,hφV,c,R,hR,?_,?_⟩
  · intro ψ hψ
    obtain ⟨hseg,hother,_⟩ := hgeom ψ hψ
    exact ⟨hseg,hother⟩
  · intro ψ hψ c₀ r₀ hr₀ hseg₀ hnest
    obtain ⟨hseg,hother,_⟩ := hgeom ψ hψ
    exact sourceActionCircle_eq_of_nested_enclosingCircles
      hp hp1 ψ n c₀ c r₀ R hr₀ hR hseg₀ hseg hnest hother

end NLS.ZakharovShabat
