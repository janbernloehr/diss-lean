import NLS.ZakharovShabat.SourcePsiContourAnalytic
import NLS.ZakharovShabat.SourceActionContourHomotopy
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-!
# Contour invariance of the psi equation

The psi integrand is holomorphic off all periodic gap segments. A
smooth gap-avoiding homotopy therefore preserves its contour integral.
In particular, nested enclosing circles, or two circles inside one
common outer isolating circle, give the same equation coordinate.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat

/-- At fixed root and source inputs, the psi integrand is holomorphic
in the spectral variable outside the periodic gap segments. -/
theorem analyticOnNhd_sourcePsiContourIntegrand_fixed
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (ψ : CoeffPair p) :
    AnalyticOnNhd ℂ
      (fun z => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)))
      (sourceCanonicalRootDomain hp hp1 ψ) := by
  intro z hz
  have hnum : AnalyticAt ℂ (fun w => sourcePsiCandidate n (w,a)) z :=
    ((analyticOnNhd_sourcePsiCandidate hp hp1 n)
      (z,a) (mem_univ _)).comp
        (f := fun w : ℂ => (w,a))
        (analyticAt_id.prod analyticAt_const)
  have hden := sourceCanonicalRoot_analyticOnNhd hp hp1 ψ z hz
  change AnalyticAt ℂ
    (fun w => sourcePsiCandidate n (w,a) /
      sourceCanonicalRoot hp hp1 ψ w) z
  exact hnum.div hden
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z hz)

/-- A smooth loop homotopy avoiding all periodic gaps preserves the
psi contour integral for fixed source and root inputs. -/
theorem sourcePsiContour_eq_of_homotopy_range
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (H : (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ)).Homotopy
      (NLS.ComplexAnalysis.circlePath c₁ r₁))
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    sourcePsiContour hp hp1 n a ψ c₀ r₀ =
      sourcePsiContour hp hp1 n a ψ c₁ r₁ := by
  let f : ℂ → ℂ := fun z =>
    sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  have hcurve := NLS.ComplexAnalysis.curveIntegral_eq_of_holomorphic_homotopy
    f H hloop (t := range H)
    (by
      intro s _ u _
      exact ⟨(s,u),rfl⟩)
    (by
      intro z hz
      have hz' : z ∈ range H := by
        simpa only [hclosed.closure_eq] using hz
      exact (analyticOnNhd_sourcePsiContourIntegrand_fixed
        hp hp1 n a ψ z (havoid hz')).differentiableAt)
    hcontdiff
  have hcircle : (∮ z in C(c₀,r₀), f z) =
      ∮ z in C(c₁,r₁), f z := by
    calc
      (∮ z in C(c₀,r₀), f z) =
          ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₀ r₀,
            NLS.ComplexAnalysis.holomorphicOneForm f z :=
        (NLS.ComplexAnalysis.curveIntegral_circlePath f c₀ r₀).symm
      _ = ∫ᶜ z in NLS.ComplexAnalysis.circlePath c₁ r₁,
            NLS.ComplexAnalysis.holomorphicOneForm f z := hcurve
      _ = (∮ z in C(c₁,r₁), f z) :=
        NLS.ComplexAnalysis.curveIntegral_circlePath f c₁ r₁
  exact congrArg ((2*Real.pi : ℂ)⁻¹ * ·) hcircle

/-- Nested circles enclosing one periodic gap give equal psi contours
when the outer closed disc avoids all other periodic gaps. -/
theorem sourcePsiContour_eq_of_nested_enclosingCircles
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hother : closedBall c₁ r₁ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourcePsiContour hp hp1 n a ψ c₀ r₀ =
      sourcePsiContour hp hp1 n a ψ c₁ r₁ := by
  let H := ContinuousMap.Homotopy.affine
    (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ))
    (NLS.ComplexAnalysis.circlePath c₁ r₁ : C(I, ℂ))
  have havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨⟨s,u⟩,rfl⟩ j
    by_cases hj : j = m
    · subst j
      intro hz
      exact (NLS.ComplexAnalysis.affineCircleHomotopy_ne_of_mem_both_balls
        c₀ c₁ _ r₀ r₁ (hseg₀ hz) (hseg₁ hz) s u) rfl
    · have hball : H (s,u) ∈ closedBall c₁ r₁ :=
        NLS.ComplexAnalysis.affineCircleHomotopy_mem_outer_closedBall
          c₀ c₁ r₀ r₁ hr₀.le hr₁.le hnest s u
      exact (hother hball) j hj
  exact sourcePsiContour_eq_of_homotopy_range hp hp1 n a ψ
    c₀ c₁ r₀ r₁ H
    (NLS.ComplexAnalysis.affineHomotopy_loop
      (γ₁ := NLS.ComplexAnalysis.circlePath c₀ r₀)
      (γ₂ := NLS.ComplexAnalysis.circlePath c₁ r₁))
    havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₀ r₀)
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₁ r₁))

/-- Two possibly nonnested circles enclosing the same gap give equal
psi contours when both lie inside a common outer isolating circle. -/
theorem sourcePsiContour_eq_of_common_outer
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c₀ c₁ c : ℂ) (r₀ r₁ R : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hR : 0 < R)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₁ r₁)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hnest₀ : closedBall c₀ r₀ ⊆ closedBall c R)
    (hnest₁ : closedBall c₁ r₁ ⊆ closedBall c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourcePsiContour hp hp1 n a ψ c₀ r₀ =
      sourcePsiContour hp hp1 n a ψ c₁ r₁ := by
  calc
    sourcePsiContour hp hp1 n a ψ c₀ r₀ =
        sourcePsiContour hp hp1 n a ψ c R :=
      sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n m a ψ
        c₀ c r₀ R hr₀ hR hseg₀ hseg hnest₀ hother
    _ = sourcePsiContour hp hp1 n a ψ c₁ r₁ :=
      (sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n m a ψ
        c₁ c r₁ R hr₁ hR hseg₁ hseg hnest₁ hother).symm

/-- On two contours compared through a common outer isolating circle,
the corresponding scalar psi equation coordinates agree. -/
theorem sourcePsiEquationCoordinate_eq_of_common_outer
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c₀ c₁ c : ℂ) (r₀ r₁ R : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hR : 0 < R)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₁ r₁)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hnest₀ : closedBall c₀ r₀ ⊆ closedBall c R)
    (hnest₁ : closedBall c₁ r₁ ⊆ closedBall c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourcePsiEquationCoordinate hp hp1 n m a ψ c₀ r₀ =
      sourcePsiEquationCoordinate hp hp1 n m a ψ c₁ r₁ := by
  exact congrArg
    (fun z : ℂ => ((n-m : ℤ) : ℂ) * (2*Real.pi : ℂ) * z)
    (sourcePsiContour_eq_of_common_outer hp hp1 n m a ψ
      c₀ c₁ c r₀ r₁ R hr₀ hr₁ hR hseg₀ hseg₁ hseg
      hnest₀ hnest₁ hother)

end NLS.ZakharovShabat
