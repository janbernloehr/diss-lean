import NLS.ZakharovShabat.SourceNormalizedActionCircleAnalytic
import NLS.ZakharovShabat.SourceCriticalRootRatioAnyCircleZero
import NLS.ZakharovShabat.SourceNormalizedActionNoncollapsed

/-!
# Normalized contour candidate for the glued indexed action

The analytic contour candidate is placed on the very circle of an
indexed-action ball chart. Vanishing of the unweighted quotient on
that prescribed circle permits recentering. Thus the glued complex
action equals the squared gap times this candidate near every
real-type source, including on the complex collapsed-gap locus.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Locally around a real-type source, the glued indexed action is
the squared periodic gap times a differentiable fixed-circle
candidate. On noncollapsed gaps this candidate is the raw quotient. -/
theorem exists_local_sourceComplexAction_normalizedCircleCandidate
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        DifferentiableOn ℂ
          (sourceNormalizedActionCircleCandidate hp hp1 n c R) V ∧
        (∀ ψ ∈ V,
          AnalyticAt ℂ (fun χ : CoeffPair p =>
            (sourcePeriodicGapDisplacement hp hp1 χ n)^2) ψ) ∧
        ∀ ψ ∈ V,
          sourceComplexAction hp hp1 n ψ =
            (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
              sourceNormalizedActionCircleCandidate hp hp1 n c R ψ ∧
          ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2 ≠ 0 →
            sourceRawNormalizedAction hp hp1 n ψ =
              sourceNormalizedActionCircleCandidate hp hp1 n c R ψ) := by
  obtain ⟨ch,hcenter⟩ :=
    exists_sourceRealActionBallChart_centered hp hp1 n φ hφ
  let c := ch.spectralCenter
  let R := ch.spectralRadius
  let V₀ := ball ch.center ch.radius
  have hφV₀ : φ ∈ V₀ := by
    change φ ∈ ball ch.center ch.radius
    rw [hcenter]
    exact mem_ball_self ch.radius_pos
  obtain ⟨V₁,hV₁open,hφV₁,hV₁sub,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_on_givenCircle
      hp hp1 φ hφ n V₀ isOpen_ball hφV₀ c R ch.spectralRadius_pos
      ch.geometry
  let F := sourceNormalizedActionCircleIntegrandJoint hp hp1 n
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hDopen : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  have hcircle (z : ℂ) (hz : z ∈ sphere c R) : (z,φ) ∈ D := by
    obtain ⟨hseg,hother⟩ := ch.geometry φ hφV₀
    have hdom : z ∈ sourceCanonicalRootDomain hp hp1 φ :=
      sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n c R
        hseg hother hz
    exact analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_realType
      hp hp1 n φ hφ z hdom
  obtain ⟨V₂,hV₂open,hφV₂,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hF c R φ hcircle
  obtain ⟨W₁,hW₁open,hreal₁,hEdata⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  obtain ⟨W₂,hW₂open,_,hreal₂,hexact⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  obtain ⟨W₃,hW₃open,_,hreal₃,hqdata⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  let V := (((V₁ ∩ V₂) ∩ W₁) ∩ W₂) ∩ W₃
  have hVopen : IsOpen V :=
    (((hV₁open.inter hV₂open).inter hW₁open).inter hW₂open).inter hW₃open
  have hφV : φ ∈ V :=
    ⟨⟨⟨⟨hφV₁,hφV₂⟩,hreal₁ hφ⟩,hreal₂ hφ⟩,hreal₃ hφ⟩
  refine ⟨V,hVopen,hφV,c,R,ch.spectralRadius_pos,?_,?_,?_,?_⟩
  · intro ψ hψ
    exact ch.geometry ψ (hV₁sub hψ.1.1.1.1)
  · intro ψ hψ
    have hdom : ∀ b ∈ V, ∀ θ : ℝ,
        (circleMap c R θ,b) ∈ D := by
      intro b hb θ
      exact (hbound (circleMap c R θ)
        (circleMap_mem_sphere c ch.spectralRadius_pos.le θ) b hb.1.1.1.2).1
    have hdbound : ∀ b ∈ V, ∀ θ : ℝ,
        ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M := by
      intro b hb θ
      exact (hbound (circleMap c R θ)
        (circleMap_mem_sphere c ch.spectralRadius_pos.le θ) b hb.1.1.1.2).2
    have hdiff := NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
      F D hDopen hF c R ch.spectralRadius_pos.le V hVopen ψ hψ M hdom hdbound
    have hfun : sourceNormalizedActionCircleCandidate hp hp1 n c R =
        (fun b : CoeffPair p => -(Real.pi : ℂ)⁻¹ *
          ∮ z in C(c,R), F (z,b)) := by
      funext b
      exact sourceNormalizedActionCircleCandidate_eq_integral hp hp1 n c R b
    rw [hfun]
    exact (hdiff.const_mul (-(Real.pi : ℂ)⁻¹)).differentiableWithinAt
  · intro ψ hψ
    have hq := (hqdata ψ hψ.2 n).2
    exact hq.congr (Filter.Eventually.of_forall fun χ => by
      simp only [sourcePeriodicGapDisplacement_apply])
  · intro ψ hψ
    have hψch : ψ ∈ V₀ := hV₁sub hψ.1.1.1.1
    obtain ⟨hseg,hother⟩ := ch.geometry ψ hψch
    have hcircleψ : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
    have hzseg : ∀ z ∈ sphere c R,
        z ∉ sourcePeriodicSegment hp hp1 ψ n := by
      intro z hz
      exact hcircleψ hz n
    have hE : AnalyticOnNhd ℂ
        (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R) := by
      intro z hz
      exact hEdata ψ hψ.1.1.2 n z (hother hz)
    have hcircleFactor := sourceActionCircle_eq_squaredGap_mul_kernel
      hp hp1 ψ n c R
      (canonicalCriticalGapQuotient hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      ch.spectralRadius_pos.le hcircleψ hzseg
      (hzero ψ hψ.1.1.1.1) hE (hexact ψ hψ.1.2 n).2
    have hglue := sourceComplexAction_eq_chart hp hp1 n ch ψ hψch
    have hfactor : sourceComplexAction hp hp1 n ψ =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
          sourceNormalizedActionCircleCandidate hp hp1 n c R ψ :=
      hglue.trans hcircleFactor
    refine ⟨hfactor,?_⟩
    intro hqne
    unfold sourceRawNormalizedAction
    rw [hfactor]
    exact mul_div_cancel_left₀ _ hqne

end NLS.ZakharovShabat
