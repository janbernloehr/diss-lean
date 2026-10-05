import NLS.ZakharovShabat.SourceAbelianMomentRealContourComparison

/-! # Contour comparison for arbitrary holomorphic gap integrands

The real-centered isolating-circle comparison applies to any function
analytic off the periodic gaps, in particular to primitive powers.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat

/-- Smooth loop homotopies in the gap complement preserve the integral. -/
theorem sourceGapCircleIntegral_eq_of_homotopy_range
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (sourceCanonicalRootDomain hp hp1 ψ))
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (H : (NLS.ComplexAnalysis.circlePath c₀ r₀ : C(I, ℂ)).Homotopy
      (NLS.ComplexAnalysis.circlePath c₁ r₁))
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    (∮ z in C(c₀,r₀), f z) =
      (∮ z in C(c₁,r₁), f z) := by
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
      exact (hf z (havoid hz')).differentiableAt)
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
theorem sourceGapCircleIntegral_eq_of_nested_enclosingCircles
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (ψ : CoeffPair p) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (sourceCanonicalRootDomain hp hp1 ψ))
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hother : closedBall c₁ r₁ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    (∮ z in C(c₀,r₀), f z) =
      (∮ z in C(c₁,r₁), f z) := by
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
  exact sourceGapCircleIntegral_eq_of_homotopy_range hp hp1 ψ f hf
    c₀ c₁ r₀ r₁ H
    (NLS.ComplexAnalysis.affineHomotopy_loop
      (γ₁ := NLS.ComplexAnalysis.circlePath c₀ r₀)
      (γ₂ := NLS.ComplexAnalysis.circlePath c₁ r₁))
    havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₀ r₀)
      (NLS.ComplexAnalysis.circlePath_contDiffOn c₁ r₁))


/-- Real-centered circles enclosing the same gap give the same integral. -/
theorem sourceGapCircleIntegral_eq_of_realCentered_enclosingCircles
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (ψ : CoeffPair p) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (sourceCanonicalRootDomain hp hp1 ψ)) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hc₀ : c₀.im = 0) (hc₁ : c₁.im = 0)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₁ r₁)
    (hother₀ : closedBall c₀ r₀ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hother₁ : closedBall c₁ r₁ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    (∮ z in C(c₀,r₀), f z) =
      (∮ z in C(c₁,r₁), f z) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let c : ℂ := ((((l.re+r.re)/2 : ℝ) : ℂ))
  let d : ℝ := (r.re-l.re)/2
  have hc₀' : (c₀.re : ℂ) = c₀ := by
    apply Complex.ext
    · rfl
    · simpa using hc₀.symm
  have hc₁' : (c₁.re : ℂ) = c₁ := by
    apply Complex.ext
    · rfl
    · simpa using hc₁.symm
  have hseg₀' : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (c₀.re : ℂ) r₀ := by simpa only [hc₀'] using hseg₀
  have hseg₁' : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (c₁.re : ℂ) r₁ := by simpa only [hc₁'] using hseg₁
  obtain ⟨ρ₀,hρ₀,hnest₀⟩ :=
    exists_sourceStandardRoot_innerMidpointDisc_of_realCenteredCircle
      hp hp1 ψ hreal m c₀.re r₀ hseg₀'
  obtain ⟨ρ₁,hρ₁,hnest₁⟩ :=
    exists_sourceStandardRoot_innerMidpointDisc_of_realCenteredCircle
      hp hp1 ψ hreal m c₁.re r₁ hseg₁'
  let ρ : ℝ := min ρ₀ ρ₁
  have hdρ : d < ρ := lt_min hρ₀ hρ₁
  have hd : 0 ≤ d := by
    have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ)).2.1 m)
    change l.re ≤ r.re at hle
    dsimp only [d]
    linarith
  have hρ : 0 < ρ := lt_of_le_of_lt hd hdρ
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c ρ := by
    have h := sourcePeriodicSegment_subset_midpoint_ball
      hp hp1 ψ hreal m (ρ-d) (sub_pos.mpr hdρ)
    have heq : d+(ρ-d)=ρ := by ring
    simpa only [c,d,l,r,heq] using h
  have hnest₀' : closedBall c ρ ⊆ closedBall c₀ r₀ := by
    have hsub : closedBall c ρ ⊆ closedBall c ρ₀ := by
      intro z hz
      exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (min_le_left _ _))
    have hnest₀'' : closedBall c ρ₀ ⊆ ball c₀ r₀ := by
      simpa only [c,l,r,hc₀'] using hnest₀
    exact hsub.trans (hnest₀''.trans ball_subset_closedBall)
  have hnest₁' : closedBall c ρ ⊆ closedBall c₁ r₁ := by
    have hsub : closedBall c ρ ⊆ closedBall c ρ₁ := by
      intro z hz
      exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (min_le_right _ _))
    have hnest₁'' : closedBall c ρ₁ ⊆ ball c₁ r₁ := by
      simpa only [c,l,r,hc₁'] using hnest₁
    exact hsub.trans (hnest₁''.trans ball_subset_closedBall)
  calc
    (∮ z in C(c₀,r₀), f z) =
        (∮ z in C(c,ρ), f z) :=
      (sourceGapCircleIntegral_eq_of_nested_enclosingCircles
        hp hp1 m ψ f hf c c₀ ρ r₀ hρ hr₀
        hseg hseg₀ hnest₀' hother₀).symm
    _ = (∮ z in C(c₁,r₁), f z) :=
      sourceGapCircleIntegral_eq_of_nested_enclosingCircles
        hp hp1 m ψ f hf c c₁ ρ r₁ hρ hr₁
        hseg hseg₁ hnest₁' hother₁


end NLS.ZakharovShabat
