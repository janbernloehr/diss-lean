import NLS.ZakharovShabat.SourceAbelianMomentCircle
import NLS.ZakharovShabat.SourcePsiEquationContourHomotopy

/-! # Contour deformation for the Section 20 moments

Holomorphy of the actual primitive and psi quotient gives invariance
under smooth gap-avoiding loop homotopies, including nested circles
and circles with a common outer isolating disc.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat

/-- The moment integrand is holomorphic off the gaps at each source
admitting an actual spectral chart. -/
theorem analyticOnNhd_sourceAbelianMomentIntegrand_fixed
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (q : ℕ) (a : Coeff p) (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ) :
    AnalyticOnNhd ℂ (fun z => sourceAbelianMomentIntegrand hp hp1 W n k q (z,(a,ψ)))
      (sourceCanonicalRootDomain hp hp1 ψ) := by
  intro z hz
  exact ((sourceFullAbelianPrimitive_spectral_analytic D k z
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hz)).pow q).mul
      (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n a ψ z hz)

/-- A smooth loop homotopy avoiding all periodic gaps preserves the
moment circle integral for fixed source and root inputs. -/
theorem sourceAbelianMomentCircle_eq_of_homotopy_range
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (k : ℤ) (q : ℕ)
    (n : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (H : (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ)).Homotopy
      (NLS.ComplexAnalysis.circlePath c₁ r₁))
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    sourceAbelianMomentCircle hp hp1 W n k q a ψ c₀ r₀ =
      sourceAbelianMomentCircle hp hp1 W n k q a ψ c₁ r₁ := by
  let f : ℂ → ℂ := fun z =>
    sourceAbelianMomentIntegrand hp hp1 W n k q (z,(a,ψ))
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
      exact (analyticOnNhd_sourceAbelianMomentIntegrand_fixed
        hp hp1 W n k q a ψ D z (havoid hz')).differentiableAt)
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
  exact hcircle

/-- Nested circles enclosing one periodic gap give equal moment circles
when the outer closed disc avoids all other periodic gaps. -/
theorem sourceAbelianMomentCircle_eq_of_nested_enclosingCircles
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (k : ℤ) (q : ℕ)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hother : closedBall c₁ r₁ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceAbelianMomentCircle hp hp1 W n k q a ψ c₀ r₀ =
      sourceAbelianMomentCircle hp hp1 W n k q a ψ c₁ r₁ := by
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
  exact sourceAbelianMomentCircle_eq_of_homotopy_range hp hp1 W k q n a ψ D
    c₀ c₁ r₀ r₁ H
    (NLS.ComplexAnalysis.affineHomotopy_loop
      (γ₁ := NLS.ComplexAnalysis.circlePath c₀ r₀)
      (γ₂ := NLS.ComplexAnalysis.circlePath c₁ r₁))
    havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₀ r₀)
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₁ r₁))

/-- Two possibly nonnested circles enclosing the same gap give equal
moment circles when both lie inside a common outer isolating circle. -/
theorem sourceAbelianMomentCircle_eq_of_common_outer
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (k : ℤ) (q : ℕ)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c₀ c₁ c : ℂ) (r₀ r₁ R : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hR : 0 < R)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₁ r₁)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hnest₀ : closedBall c₀ r₀ ⊆ closedBall c R)
    (hnest₁ : closedBall c₁ r₁ ⊆ closedBall c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceAbelianMomentCircle hp hp1 W n k q a ψ c₀ r₀ =
      sourceAbelianMomentCircle hp hp1 W n k q a ψ c₁ r₁ := by
  calc
    sourceAbelianMomentCircle hp hp1 W n k q a ψ c₀ r₀ =
        sourceAbelianMomentCircle hp hp1 W n k q a ψ c R :=
      sourceAbelianMomentCircle_eq_of_nested_enclosingCircles hp hp1 W k q n m a ψ D
        c₀ c r₀ R hr₀ hR hseg₀ hseg hnest₀ hother
    _ = sourceAbelianMomentCircle hp hp1 W n k q a ψ c₁ r₁ :=
      (sourceAbelianMomentCircle_eq_of_nested_enclosingCircles hp hp1 W k q n m a ψ D
        c₁ c r₁ R hr₁ hR hseg₁ hseg hnest₁ hother).symm

/-- The ambient neighborhood used to construct the primitive does not
change a moment on a circle in the common gap complement. -/
theorem sourceAbelianMomentCircle_independent_neighborhood
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W V : Set (CoeffPair p))
    (n k : ℤ) (m : ℕ) (a : Coeff p) (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ) (E : SourceAbelianSpectralChart hp hp1 V ψ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianMomentCircle hp hp1 W n k m a ψ c R =
      sourceAbelianMomentCircle hp hp1 V n k m a ψ c R := by
  apply circleIntegral.integral_congr hR
  intro z hz
  dsimp only [sourceAbelianMomentIntegrand]
  rw [sourceFullAbelianPrimitive_independent_neighborhood D E k z
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hcircle hz))]

end NLS.ZakharovShabat
