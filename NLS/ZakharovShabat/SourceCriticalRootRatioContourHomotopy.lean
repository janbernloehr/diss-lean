import NLS.ZakharovShabat.SourceCriticalRootRatioGapSideIntegral
import NLS.ComplexAnalysis.HolomorphicCurveHomotopy
import NLS.ComplexAnalysis.ContinuousSmoothLoopHomotopy
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Contour invariance of the critical-root quotient

The discriminant derivative divided by the full canonical root is
holomorphic off all closed periodic gap segments. Its integral is
therefore unchanged by a smooth gap-avoiding loop homotopy, and by
radial motion through an annulus free of all gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full canonical root cannot vanish off all gap segments. -/
theorem sourceCanonicalRoot_ne_zero_off_gaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceCanonicalRoot hp hp1 ψ z ≠ 0 := by
  have hs := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ 0 z (hz 0)
  have ho := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z 0
    (fun m _ => hz m)
  rw [sourceCanonicalRoot_eq_omitted hp hp1 0 ψ z]
  have htwo : (2:ℂ) ≠ 0 := by norm_num
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo I_ne_zero) hs) ho

/-- The actual critical-root quotient is analytic on the entire
complement of the periodic gap segments. -/
theorem sourceCriticalRootRatio_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    AnalyticOnNhd ℂ
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
      (sourceCanonicalRootDomain hp hp1 ψ) := by
  intro z hz
  have hnum := analyticOnNhd_discriminant_derivative hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) z (mem_univ z)
  have hden := sourceCanonicalRoot_analyticOnNhd hp hp1 ψ z hz
  exact hnum.div hden (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z hz)

/-- For real-type sources, the complement of all periodic gap segments
is an open spectral domain. -/
theorem isOpen_sourceCanonicalRootDomain_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    IsOpen (sourceCanonicalRootDomain hp hp1 ψ) := by
  obtain ⟨W,_,_,hWreal,hopen,_⟩ :=
    exists_global_source_analytic_canonicalRoot hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  have heq : sourceCanonicalRootDomain hp hp1 ψ =
      (fun z : ℂ => (z,ψ)) ⁻¹'
        sourceCanonicalRootJointDomain hp hp1 W := by
    ext z
    change (∀ n, z ∉ sourcePeriodicSegment hp hp1 ψ n) ↔
      ψ ∈ W ∧ (∀ n, z ∉ sourcePeriodicSegment hp hp1 ψ n)
    exact ⟨fun hz => ⟨hψ,hz⟩, And.right⟩
  rw [heq]
  exact hopen.preimage (by fun_prop)

/-- A smooth homotopy of closed loops avoiding every gap preserves
the full critical-root quotient integral. -/
theorem sourceCriticalRootRatio_curveIntegral_eq_of_homotopy_range
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) =
    ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z := by
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  apply NLS.ComplexAnalysis.curveIntegral_eq_of_holomorphic_homotopy
    (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w)
    H hloop (t := range H)
  · intro s _ u _
    exact ⟨(s,u), rfl⟩
  · intro z hz
    have hz' : z ∈ range H := by simpa only [hclosed.closure_eq] using hz
    exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
      (havoid hz')).differentiableAt
  · exact hcontdiff

/-- A continuous homotopy with twice-smooth gap-avoiding loop slices
also preserves the quotient integral at a real-type source. -/
theorem sourceCriticalRootRatio_curveIntegral_eq_of_continuous_smooth_homotopy
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hsmooth : ∀ s : I,
      ContDiffOn ℝ 2 (NLS.ComplexAnalysis.homotopyLoop H hloop s).extend
        (Icc 0 1))
    (havoid : ∀ s u : I, H (s,u) ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) =
    ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z := by
  apply NLS.ComplexAnalysis.curveIntegral_eq_of_continuous_smooth_loop_homotopy
    (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w)
    (sourceCanonicalRootDomain hp hp1 ψ)
    (isOpen_sourceCanonicalRootDomain_of_realType hp hp1 ψ hreal)
    (fun z hz => (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z hz).differentiableAt)
    H hloop hsmooth havoid

/-- The quotient circle integral is unchanged between concentric
circles when the closed annulus between them avoids every gap. -/
theorem circleIntegral_sourceCriticalRootRatio_eq_of_annulus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (havoid : closedBall c R \ ball c r ⊆
      sourceCanonicalRootDomain hp hp1 ψ) :
    (∮ z in C(c, R),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) =
    ∮ z in C(c, r),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z := by
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  have hf := sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ
  have hc : ContinuousOn f (closedBall c R \ ball c r) := by
    intro z hz
    exact (hf z (havoid hz)).continuousAt.continuousWithinAt
  have hd : ∀ z ∈ (ball c R \ closedBall c r) \ (∅ : Set ℂ),
      DifferentiableAt ℂ f z := by
    intro z hz
    have hz' : z ∈ closedBall c R \ ball c r :=
      ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩
    exact (hf z (havoid hz')).differentiableAt
  exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (s := ∅) Set.countable_empty hc hd

/-- Radial deformation is valid when the inner circle encloses the
selected gap and the outer filled disc avoids all other gaps. -/
theorem circleIntegral_sourceCriticalRootRatio_eq_of_isolated_annulus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (∮ z in C(c, R),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) =
    ∮ z in C(c, r),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z := by
  apply circleIntegral_sourceCriticalRootRatio_eq_of_annulus
    hp hp1 ψ c r R hr hrR
  intro z hz m
  by_cases hm : m = n
  · subst m
    intro hmem
    exact hz.2 (hseg hmem)
  · exact (hother hz.1) m hm

end NLS.ZakharovShabat
