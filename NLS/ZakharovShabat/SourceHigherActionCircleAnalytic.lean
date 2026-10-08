import NLS.ZakharovShabat.SourceHigherActionBoundary
import NLS.ZakharovShabat.SourceGapContourComparison
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Analyticity and compatibility of higher-action contours -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Polynomial weights preserve Banach analyticity of the defining contour. -/
theorem sourceHigherActionCircle_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) {W V : Set (CoeffPair p)}
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hq : AnalyticOnNhd ℂ (sourceCriticalRootRatioJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W))
    (hV : IsOpen V) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ ψ ∈ V, ∀ z ∈ sphere c R,
      (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W) (k : ℕ) :
    AnalyticOnNhd ℂ (fun ψ => sourceHigherActionCircle hp hp1 ψ c R k) V := by
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic
    (fun t : ℂ × CoeffPair p => t.1^(k+1)*sourceCriticalRootRatioJoint hp hp1 t)
    hD (fun t ht => (analyticAt_fst.pow (k+1)).mul (hq t ht)) c R hR hV hc
  exact fun ψ hψ => analyticAt_const.mul (hi ψ hψ)

/-- Any two real-centered isolating circles give the same higher action
at a real source, at every level. -/
theorem sourceHigherActionCircle_eq_of_realCentered_enclosingCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (k : ℕ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ) (hc₀ : c₀.im = 0) (hc₁ : c₁.im = 0)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₁ r₁)
    (hother₀ : closedBall c₀ r₀ ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hother₁ : closedBall c₁ r₁ ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceHigherActionCircle hp hp1 ψ c₀ r₀ k = sourceHigherActionCircle hp hp1 ψ c₁ r₁ k := by
  unfold sourceHigherActionCircle
  congr 1
  exact sourceGapCircleIntegral_eq_of_realCentered_enclosingCircles hp hp1 n ψ _
    (fun z hz => (analyticAt_id.pow (k+1)).mul (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z hz))
    hreal c₀ c₁ r₀ r₁ hc₀ hc₁ hr₀ hr₁ hseg₀ hseg₁ hother₀ hother₁

/-- The filled quotient removes a collapsed complex gap at all higher levels.
One almost-real source neighborhood works for every index and order. -/
theorem exists_global_sourceHigherActionCircle_zero_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ, sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
        ∀ c : ℂ, ∀ R : ℝ, 0 ≤ R →
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
          sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ →
          ∀ k : ℕ, sourceHigherActionCircle hp hp1 ψ c R k = 0 := by
  obtain ⟨W,hW,hreal,hdata⟩ := exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro ψ hψ n hgap c R hR hfilled hc k
  let f := sourceCriticalRootRatioExtension hp hp1 n ψ
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => z^(k+1)*f z) (closedBall c R) :=
    fun z hz => (analyticAt_id.pow (k+1)).mul ((hdata ψ hψ n hgap).1 z (hfilled hz))
  have hzero := (hf.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR
  have he : (∮ z in C(c,R), z^(k+1)*sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      ∮ z in C(c,R), z^(k+1)*f z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    change z^(k+1)*(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z) = z^(k+1)*f z
    dsimp only [f]
    rw [(hdata ψ hψ n hgap).2 z (hc hz)]
  rw [sourceHigherActionCircle,he,hzero,mul_zero]

end NLS.ZakharovShabat
