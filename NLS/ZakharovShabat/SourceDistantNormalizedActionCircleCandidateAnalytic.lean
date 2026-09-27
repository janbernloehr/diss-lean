import NLS.ZakharovShabat.SourceDistantNormalizedActionCircleIntegrandAnalytic
import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleLocalComplexAgreement

/-!
# A common differentiability domain for distant circle candidates

Joint analyticity of the rationalized integrand on each free circle
permits differentiation under the contour integral at every complex
source in one neighborhood, uniformly in the choice of distant index.
The resulting common domain is independent of the index.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Joint analyticity at all points of one circle makes the
normalized-action circle candidate differentiable at its source,
without a real-type assumption. -/
theorem differentiableAt_sourceNormalizedActionCircleCandidate_of_jointAnalytic
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (ψ : CoeffPair p)
    (hcircle : ∀ z ∈ sphere c R,
      AnalyticAt ℂ (sourceNormalizedActionCircleIntegrandJoint hp hp1 n) (z,ψ)) :
    DifferentiableAt ℂ (sourceNormalizedActionCircleCandidate hp hp1 n c R) ψ := by
  let F := sourceNormalizedActionCircleIntegrandJoint hp hp1 n
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hDopen : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  have hcircleF (z : ℂ) (hz : z ∈ sphere c R) : (z,ψ) ∈ D :=
    hcircle z hz
  obtain ⟨V,hVopen,hψV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hF c R ψ hcircleF
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
  have hfun : sourceNormalizedActionCircleCandidate hp hp1 n c R =
      (fun b : CoeffPair p => -(Real.pi:ℂ)⁻¹ *
        ∮ z in C(c,R), F (z,b)) := by
    funext b
    exact sourceNormalizedActionCircleCandidate_eq_integral hp hp1 n c R b
  rw [hfun]
  exact hdiff.const_mul (-(Real.pi:ℂ)⁻¹)

/-- One open complex source neighborhood makes every distant
free-centered normalized-action circle candidate differentiable. -/
theorem exists_local_source_distantNormalizedActionCircleCandidate_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ n : ℤ, K < n.natAbs →
        DifferentiableOn ℂ
          (sourceNormalizedActionCircleCandidate hp hp1 n
            ((Real.pi:ℂ)*n) (Real.pi/8)) V := by
  obtain ⟨K,V,hVopen,hφV,hjoint⟩ :=
    exists_local_source_distantNormalizedActionCircleIntegrand_jointAnalytic
      hp hp1 φ hreal
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro n hn ψ hψ
  exact (differentiableAt_sourceNormalizedActionCircleCandidate_of_jointAnalytic
    hp hp1 n ((Real.pi:ℂ)*n) (Real.pi/8) (by positivity) ψ
      (hjoint ψ hψ n hn)).differentiableWithinAt

end NLS.ZakharovShabat
