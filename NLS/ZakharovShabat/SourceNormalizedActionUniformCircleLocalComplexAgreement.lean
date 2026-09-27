import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleRealAgreement
import NLS.ZakharovShabat.SourceRealActionLocalOverlap

/-!
# Local complex agreement for each distant common circle

For a prescribed valid circle, joint analyticity of the rationalized
integrand makes its normalized contour candidate differentiable near
a real-type source. The real-form identity principle then extends the
common-circle real agreement to a complex neighborhood for each fixed
distant index. Uniformity of these neighborhoods is a separate step.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A prescribed circle lying in the root domain at a real-type base
source gives a complex-differentiable normalized contour candidate
on a source neighborhood. -/
theorem exists_local_sourceNormalizedActionCircleCandidate_differentiableOn_givenCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      DifferentiableOn ℂ
        (sourceNormalizedActionCircleCandidate hp hp1 n c R) V := by
  let F := sourceNormalizedActionCircleIntegrandJoint hp hp1 n
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hDopen : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  have hcircleF (z : ℂ) (hz : z ∈ sphere c R) : (z,φ) ∈ D :=
    analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_realType
      hp hp1 n φ hφ z (hcircle hz)
  obtain ⟨V,hVopen,hφV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hF c R φ hcircleF
  refine ⟨V,hVopen,hφV,?_⟩
  intro ψ hψ
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
    F D hDopen hF c R hR.le V hVopen ψ hψ M hdom hdbound
  have hfun : sourceNormalizedActionCircleCandidate hp hp1 n c R =
      (fun b : CoeffPair p => -(Real.pi:ℂ)⁻¹ *
        ∮ z in C(c,R), F (z,b)) := by
    funext b
    exact sourceNormalizedActionCircleCandidate_eq_integral hp hp1 n c R b
  rw [hfun]
  exact (hdiff.const_mul (-(Real.pi:ℂ)⁻¹)).differentiableWithinAt

/-- For every sufficiently distant signed index, the free-centered
candidate equals the chart-independent normalized action on a complex
source neighborhood of the base real-type potential. The cutoff and
real-agreement domain are common; the complex neighborhood may depend
on the index. -/
theorem exists_local_sourceNormalizedAction_uniform_circle_complex_agreement_at_index
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ n : ℤ, K ≤ n.natAbs →
        ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
          ∀ ψ ∈ U,
            sourceNormalizedActionCircleCandidate hp hp1 n
                ((Real.pi:ℂ)*n) (Real.pi/8) ψ =
              sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  obtain ⟨Kr,Vr,hVropen,hφVr,hreal⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_real_agreement
      hp hp1 φ hφ
  obtain ⟨Kg,Vg,_,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data hp hp1 φ hφ
  let K := max Kr Kg
  refine ⟨K,Vr,hVropen,hφVr,?_⟩
  intro n hn
  have hKr : Kr ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKg : Kg ≤ n.natAbs := le_trans (le_max_right _ _) hn
  obtain ⟨hseg,hother,_,_,_⟩ := hgeom φ hφVg n hKg
  have hcircle : sphere ((Real.pi:ℂ)*n) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 φ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n
      ((Real.pi:ℂ)*n) (Real.pi/8) hseg hother
  obtain ⟨Vc,hVcopen,hφVc,hcandDiff⟩ :=
    exists_local_sourceNormalizedActionCircleCandidate_differentiableOn_givenCircle
      hp hp1 φ hφ n ((Real.pi:ℂ)*n) (Real.pi/8)
      (by positivity) hcircle
  obtain ⟨Ve,hVeopen,hφVe,hextDiff,_⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_differentiableOn
      hp hp1 φ hφ n
  let V₀ := Vr ∩ Vc
  let V₁ := Vr ∩ Ve
  obtain ⟨U,hUopen,hφU,hUsub,hEq⟩ :=
    exists_local_eqOn_of_eqOn_realType hp φ hφ V₀ V₁
      (hVropen.inter hVcopen) (hVropen.inter hVeopen)
      ⟨hφVr,hφVc⟩ ⟨hφVr,hφVe⟩
      (sourceNormalizedActionCircleCandidate hp hp1 n
        ((Real.pi:ℂ)*n) (Real.pi/8))
      (sourceNormalizedActionComplexExtension hp hp1 n)
      (hcandDiff.mono inter_subset_right)
      (hextDiff.mono inter_subset_right)
      (by
        intro ψ hψ hψreal
        exact hreal ψ hψ.1.1 hψreal n hKr)
  refine ⟨U,hUopen,hφU,?_,?_⟩
  · intro ψ hψ
    exact (hUsub hψ).1.1
  · intro ψ hψ
    exact hEq hψ

end NLS.ZakharovShabat
