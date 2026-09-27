import NLS.ZakharovShabat.SourceDistantCriticalRootRatioCircleZero
import NLS.ZakharovShabat.SourceRealActionUniformTailCircle
import NLS.ZakharovShabat.SourceActionCircleAnalytic

/-!
# Uniform distant action charts on free-centered circles

The common free circles enclose the moving complex gaps and compute
the indexed real action on the real-type locus. Joint analyticity of
the weighted quotient gives source differentiability of their action
integrals. Hence one source ball supplies valid action charts for all
distant indices, so the glued complex action equals each free-circle
integral throughout that ball.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Joint analyticity of the weighted quotient along a fixed circle
makes its action integral differentiable at an arbitrary complex source. -/
theorem differentiableAt_sourceActionCircle_of_jointAnalytic_onCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcircle : ∀ z ∈ sphere c R,
      AnalyticAt ℂ (sourceActionIntegrandJoint hp hp1) (z,ψ)) :
    DifferentiableAt ℂ (fun χ : CoeffPair p =>
      sourceActionCircle hp hp1 χ c R) ψ := by
  let F := sourceActionIntegrandJoint hp hp1
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hDopen : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  obtain ⟨V,hVopen,hψV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hF c R ψ hcircle
  have hdom : ∀ b ∈ V, ∀ θ : ℝ,
      (circleMap c R θ,b) ∈ D := by
    intro b hb θ
    exact (hbound (circleMap c R θ)
      (circleMap_mem_sphere c hR.le θ) b hb).1
  have hdbound : ∀ b ∈ V, ∀ θ : ℝ,
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M := by
    intro b hb θ
    exact (hbound (circleMap c R θ)
      (circleMap_mem_sphere c hR.le θ) b hb).2
  have hdiff := NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
    F D hDopen hF c R hR.le V hVopen ψ hψV M hdom hdbound
  change DifferentiableAt ℂ (fun b : CoeffPair p => (Real.pi:ℂ)⁻¹ *
    ∮ z in C(c,R), F (z,b)) ψ
  exact hdiff.const_mul (Real.pi:ℂ)⁻¹

/-- On one complex source ball, the chart-independent indexed action
equals the free-centered circle action for all distant indices. -/
theorem exists_local_sourceComplexAction_eq_free_eighth_circle_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ r : ℝ, 0 < r ∧
      ∀ ψ ∈ ball φ r, ∀ n : ℤ, K ≤ n.natAbs →
        sourceComplexAction hp hp1 n ψ =
          sourceActionCircle hp hp1 ψ ((Real.pi:ℂ)*n) (Real.pi/8) := by
  obtain ⟨Kg,Vg,hVgopen,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data hp hp1 φ hreal
  obtain ⟨Kr,Vr,hVropen,hφVr,hrealAction⟩ :=
    exists_local_sourceRealAction_eq_free_eighth_circle_tail hp hp1 φ hreal
  obtain ⟨W,hWopen,_,hrealW,_,hweighted⟩ :=
    exists_global_sourceActionIntegrand_jointAnalytic hp hp1
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (((hVgopen.inter hVropen).inter hWopen).mem_nhds
      ⟨⟨hφVg,hφVr⟩,hrealW hreal⟩)
  let K := max Kg Kr
  refine ⟨K,r,hr,?_⟩
  intro ψ hψ n hn
  have hKg : Kg ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKr : Kr ≤ n.natAbs := le_trans (le_max_right _ _) hn
  let c : ℂ := (Real.pi:ℂ)*n
  let R : ℝ := Real.pi/8
  have hgeometry : ∀ χ ∈ ball φ r,
      sourcePeriodicSegment hp hp1 χ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 χ n := by
    intro χ hχ
    obtain ⟨hseg,hother,_,_,_⟩ := hgeom χ (hrsub hχ).1.1 n hKg
    exact ⟨hseg,hother⟩
  have hdiff : DifferentiableOn ℂ (fun χ : CoeffPair p =>
      sourceActionCircle hp hp1 χ c R) (ball φ r) := by
    intro χ hχ
    have hcircle : ∀ z ∈ sphere c R,
        AnalyticAt ℂ (sourceActionIntegrandJoint hp hp1) (z,χ) := by
      intro z hz
      obtain ⟨hseg,hother⟩ := hgeometry χ hχ
      have hzdom : z ∈ sourceCanonicalRootDomain hp hp1 χ :=
        sourceCanonicalRootDomain_of_enclosingCircle hp hp1 χ n c R
          hseg hother hz
      exact hweighted (z,χ) ⟨(hrsub hχ).2,hzdom⟩
    exact (differentiableAt_sourceActionCircle_of_jointAnalytic_onCircle
      hp hp1 χ c R (by positivity) hcircle).differentiableWithinAt
  let ch : SourceRealActionBallChart hp hp1 n := {
    center := φ
    center_real := hreal
    radius := r
    radius_pos := hr
    spectralCenter := c
    spectralRadius := R
    spectralRadius_pos := by positivity
    geometry := hgeometry
    differentiable := hdiff
    agrees_real := by
      intro χ hχ hχreal
      exact hrealAction χ (hrsub hχ).1.2 hχreal n hKr
  }
  exact sourceComplexAction_eq_chart hp hp1 n ch ψ hψ

end NLS.ZakharovShabat
