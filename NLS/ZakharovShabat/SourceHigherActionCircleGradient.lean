import NLS.ZakharovShabat.SourceActionCircleGradient
import NLS.ZakharovShabat.SourceHigherActionCircle

/-! Full source derivative of every actual higher action circle,
with its original level-dependent normalization. -/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem fderiv_sourceHigherActionCircle_eq_gradient_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (k : ℕ) (h : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceHigherActionCircle hp hp1 ψ c R k) φ) h =
      -(Real.pi : ℂ)⁻¹ *
        (∮ z in C(c,R),
          z^k * (fderiv ℂ (fun ψ : CoeffPair p =>
            canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
            sourceCanonicalRoot hp hp1 φ z) := by
  obtain ⟨W,_,_,hreal,hDopen,hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  let D := sourceCanonicalRootJointDomain hp hp1 W
  let F : ℂ × CoeffPair p → ℂ := fun t => t.1^(k+1)*sourceCriticalRootRatioJoint hp hp1 t
  have hweighted : AnalyticOnNhd ℂ F D := by
    intro t ht
    exact (analyticAt_fst.pow (k+1)).mul (hquot t ht)
  have hcircleD (z : ℂ) (hz : z ∈ sphere c R) : (z,φ) ∈ D :=
    ⟨hreal hφ,hcircle hz⟩
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
        sourceHigherActionCircle hp hp1 ψ c R k) φ) h =
        ((k+1 : ℂ)*(Real.pi : ℂ))⁻¹ *
          (fderiv ℂ (fun b : CoeffPair p =>
            ∮ z in C(c,R), F (z,b)) φ) h := by
    change (fderiv ℂ (fun ψ : CoeffPair p =>
      ((k+1 : ℂ)*(Real.pi : ℂ))⁻¹ * ∮ z in C(c,R), F (z,ψ)) φ) h = _
    rw [fderiv_const_mul hcircleDiff ((k+1 : ℂ)*(Real.pi : ℂ))⁻¹]
    simp [smul_eq_mul]
  have hweightedDeriv (z : ℂ) (hz : z ∈ sphere c R) :
      (fderiv ℂ (fun ψ : CoeffPair p => F (z,ψ)) φ) h =
        z^(k+1) * (fderiv ℂ (fun ψ : CoeffPair p =>
          sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h := by
    have hratioDiff : DifferentiableAt ℂ
        (fun ψ : CoeffPair p =>
          sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ :=
      ((hquot (z,φ) (hcircleD z hz)).comp
        (f := fun ψ : CoeffPair p => (z,ψ))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
    change (fderiv ℂ (fun ψ : CoeffPair p =>
      z^(k+1) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h = _
    rw [fderiv_const_mul hratioDiff (z^(k+1))]
    simp [smul_eq_mul]
  calc
    (fderiv ℂ (fun ψ : CoeffPair p =>
        sourceHigherActionCircle hp hp1 ψ c R k) φ) h =
        ((k+1 : ℂ)*(Real.pi : ℂ))⁻¹ *
          (∮ z in C(c,R),
            (fderiv ℂ (fun ψ : CoeffPair p => F (z,ψ)) φ) h) := by
      rw [haction, hcircleFDeriv]
    _ = ((k+1 : ℂ)*(Real.pi : ℂ))⁻¹ *
          (∮ z in C(c,R), z^(k+1) *
            (fderiv ℂ (fun ψ : CoeffPair p =>
              sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h) := by
      congr 1
      apply circleIntegral.integral_congr hR.le
      intro z hz
      exact hweightedDeriv z hz
    _ = _ := by
      have hvariation : (∮ z in C(c,R), z^(k+1)*
          (fderiv ℂ (fun ψ : CoeffPair p => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h)=
          -(k+1 : ℂ)*(∮ z in C(c,R), z^k *
            (fderiv ℂ (fun ψ : CoeffPair p =>
              canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
                sourceCanonicalRoot hp hp1 φ z) := by
        calc
          _ = ∮ z in C(c,R), z^(k+1)*deriv (fun w : ℂ =>
              (fderiv ℂ (fun ψ : CoeffPair p =>
                canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
                  sourceCanonicalRoot hp hp1 φ w) z := by
            apply circleIntegral.integral_congr hR.le
            intro z hz
            dsimp only
            rw [fderiv_sourceCriticalRootRatioJoint_eq_deriv_sourceDiscriminant_div_root
              hp hp1 φ hφ z (hcircle hz) h]
          _ = _ := by
            simpa only [mul_div_assoc] using
              NLS.ComplexAnalysis.circleIntegral_pow_mul_deriv_eq_neg _ _
                (analyticOnNhd_sourceDiscriminantVariation_div_root hp hp1 φ h)
                c R hR.le hcircle k
      rw [hvariation]
      have hk : (k+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp


end NLS.ZakharovShabat
