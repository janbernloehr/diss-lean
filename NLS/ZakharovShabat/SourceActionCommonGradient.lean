import NLS.ZakharovShabat.SourceCriticalRootRatioCommonFDeriv
import NLS.ZakharovShabat.SourceActionCircleGradient

/-!
# The action-circle gradient at every complex source in W

Joint analyticity on the unchanged common domain permits differentiation
under any fixed circle avoiding the gaps. The mixed derivative identity
and spectral integration by parts then give the exact negative normalized
discriminant-variation integral of equation (2.17).
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Contour integration by parts converts the source derivative of
the action integrand to the unweighted discriminant variation. -/
theorem SourceEquation2_15Data.circleIntegral_criticalRatio_sourceFDeriv_eq_neg_variation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_15Data hp hp1 W)
    (φ : CoeffPair p) (hφ : φ ∈ W)
    (h : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    (∮ z in C(c,R), z *
      (fderiv ℂ (fun ψ : CoeffPair p =>
        sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h) =
      -(∮ z in C(c,R),
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z) := by
  calc
    (∮ z in C(c,R), z *
        (fderiv ℂ (fun ψ : CoeffPair p =>
          sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h) =
        ∮ z in C(c,R), z * deriv (fun w : ℂ =>
          (fderiv ℂ (fun ψ : CoeffPair p =>
            canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
            sourceCanonicalRoot hp hp1 φ w) z := by
      apply circleIntegral.integral_congr hR
      intro z hz
      dsimp only
      rw [H.criticalRatio_source_fderiv_eq_spectral φ hφ z (hcircle hz) h]
    _ = _ := circleIntegral_mul_deriv_sourceDiscriminantVariation_div_root_eq_neg
      hp hp1 φ h c R hR hcircle

/-- The fixed-circle action's source Fréchet derivative is the
negative normalized integral of the discriminant variation over the
canonical root. -/
theorem SourceEquation2_15Data.fderiv_actionCircle_eq_gradient_integral
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_15Data hp hp1 W)
    (φ : CoeffPair p) (hφ : φ ∈ W)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (h : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceActionCircle hp hp1 ψ c R) φ) h =
      -(Real.pi : ℂ)⁻¹ *
        (∮ z in C(c,R),
          (fderiv ℂ (fun ψ : CoeffPair p =>
            canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
            sourceCanonicalRoot hp hp1 φ z) := by
  have hDopen := H.joint.1
  have hquot := H.joint.2
  let D := sourceCanonicalRootJointDomain hp hp1 W
  let F := sourceActionIntegrandJoint hp hp1
  have hweighted : AnalyticOnNhd ℂ F D := by
    intro t ht
    exact analyticAt_fst.mul (hquot t ht)
  have hcircleD (z : ℂ) (hz : z ∈ sphere c R) : (z,φ) ∈ D :=
    ⟨hφ,hcircle hz⟩
  obtain ⟨V,hVopen,hφV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hweighted c R φ hcircleD
  have hdom (b : CoeffPair p) (hb : b ∈ V) (θ : ℝ) :
      (circleMap c R θ,b) ∈ D :=
    (hbound (circleMap c R θ) (circleMap_mem_sphere c hR.le θ) b hb).1
  have hbound' (b : CoeffPair p) (hb : b ∈ V) (θ : ℝ) :
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M :=
    (hbound (circleMap c R θ) (circleMap_mem_sphere c hR.le θ) b hb).2
  have hcircleDiff : DifferentiableAt ℂ
      (fun b : CoeffPair p => ∮ z in C(c,R), F (z,b)) φ :=
    NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
      F D hDopen hweighted c R hR.le V hVopen φ hφV M hdom hbound'
  have hcircleFDeriv :=
    NLS.ComplexAnalysis.fderiv_circleIntegral_apply_of_jointAnalytic
      F D hDopen hweighted c R hR.le V hVopen φ hφV M hdom hbound' h
  have haction :
      (fderiv ℂ (fun ψ : CoeffPair p =>
        sourceActionCircle hp hp1 ψ c R) φ) h =
        (Real.pi : ℂ)⁻¹ *
          (fderiv ℂ (fun b : CoeffPair p =>
            ∮ z in C(c,R), F (z,b)) φ) h := by
    change (fderiv ℂ (fun ψ : CoeffPair p =>
      (Real.pi : ℂ)⁻¹ * ∮ z in C(c,R), F (z,ψ)) φ) h = _
    rw [fderiv_const_mul hcircleDiff (Real.pi : ℂ)⁻¹]
    simp [smul_eq_mul]
  have hweightedDeriv (z : ℂ) (hz : z ∈ sphere c R) :
      (fderiv ℂ (fun ψ : CoeffPair p => F (z,ψ)) φ) h =
        z * (fderiv ℂ (fun ψ : CoeffPair p =>
          sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h := by
    have hratioDiff : DifferentiableAt ℂ
        (fun ψ : CoeffPair p =>
          sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ :=
      ((hquot (z,φ) (hcircleD z hz)).comp
        (f := fun ψ : CoeffPair p => (z,ψ))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
    change (fderiv ℂ (fun ψ : CoeffPair p =>
      z * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h = _
    rw [fderiv_const_mul hratioDiff z]
    simp [smul_eq_mul]
  calc
    (fderiv ℂ (fun ψ : CoeffPair p =>
        sourceActionCircle hp hp1 ψ c R) φ) h =
        (Real.pi : ℂ)⁻¹ *
          (∮ z in C(c,R),
            (fderiv ℂ (fun ψ : CoeffPair p => F (z,ψ)) φ) h) := by
      rw [haction, hcircleFDeriv]
    _ = (Real.pi : ℂ)⁻¹ *
          (∮ z in C(c,R), z *
            (fderiv ℂ (fun ψ : CoeffPair p =>
              sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h) := by
      congr 1
      apply circleIntegral.integral_congr hR.le
      intro z hz
      exact hweightedDeriv z hz
    _ = _ := by
      rw [H.circleIntegral_criticalRatio_sourceFDeriv_eq_neg_variation φ hφ h c R hR.le hcircle]
      ring

end NLS.ZakharovShabat
