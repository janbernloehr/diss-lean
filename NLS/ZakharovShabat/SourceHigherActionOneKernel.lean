import NLS.ZakharovShabat.SourceHigherActionCircle
import NLS.ZakharovShabat.SourceNormalizedActionCircleAnalytic

/-! # A gap-independent kernel for the printed level-two action

The natural higher-action index is ONE. Subtracting the squared critical
point from the spectral weight uses the zero unweighted period. The
remaining factor is the ordinary rationalized kernel times z+critical.
No division by the squared gap occurs, even at complex collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceHigherActionOneKernelJoint (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (t : ℂ × CoeffPair p) : ℂ :=
  (t.1+canonicalCriticalPoints hp hp1 (periodOnePotential t.2) (periodOnePotential_mem _) n)*
    sourceNormalizedActionCircleIntegrandJoint hp hp1 n t

def sourceHigherActionOneCircleQuotient (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℂ) (R : ℝ) (ψ : CoeffPair p) : ℂ :=
  -(2*(Real.pi : ℂ))⁻¹ * ∮ z in C(c,R), sourceHigherActionOneKernelJoint hp hp1 n (z,ψ)

theorem analyticAt_sourceHigherActionOneKernelJoint_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    AnalyticAt ℂ (sourceHigherActionOneKernelJoint hp hp1 n) (z,φ) := by
  have hb := (analyticAt_sourceCanonicalCriticalPoint_of_realType hp hp1 n φ hφ).comp
    (analyticAt_snd (p := (z,φ)))
  exact (analyticAt_fst.add hb).mul
    (analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_realType hp hp1 n φ hφ z hz)

theorem sourceHigherActionCircle_one_eq_recentered
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0) (b : ℂ) :
    sourceHigherActionCircle hp hp1 ψ c R 1 =
      (2*(Real.pi : ℂ))⁻¹ * ∮ z in C(c,R), (z^2-b^2)*sourceCriticalRootRatioJoint hp hp1 (z,ψ) := by
  let f := fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hf : ContinuousOn f (sphere c R) := fun z hz =>
    (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z (hcircle hz)).continuousAt.continuousWithinAt
  have hi : CircleIntegrable (fun z => z^2*f z) c R :=
    ((continuousOn_id.pow 2).mul hf).circleIntegrable hR
  have hb : CircleIntegrable (fun z => b^2*f z) c R :=
    (continuousOn_const.mul hf).circleIntegrable hR
  have he : (∮ z in C(c,R), (z^2-b^2)*f z) = ∮ z in C(c,R), z^2*f z := by
    have hfun : (fun z => (z^2-b^2)*f z) = fun z => z^2*f z-b^2*f z := by funext z; ring
    rw [hfun,circleIntegral.integral_sub hi hb,circleIntegral.integral_const_mul]
    change _-b^2*(∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = _
    rw [hzero,mul_zero,sub_zero]
  rw [he]
  norm_num [sourceHigherActionCircle,f]

theorem sourceHigherActionCircle_one_eq_squaredGap_mul_kernel
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (R : ℝ) (B : ℂ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0)
    (hE : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R))
    (hoffset : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*B) :
    sourceHigherActionCircle hp hp1 ψ c R 1 =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2/2*
        normalizedActionCircleQuotient
          (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)
          ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2) B c R
          (fun z => (z+canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)*
            sourceCriticalRootRatioExtension hp hp1 n ψ z) := by
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n
  let q := (sourcePeriodicGapDisplacement hp hp1 ψ n)^2
  let b := canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  let F := fun z => (z+b)*E z
  have hb : b = τ+q*B := by linear_combination hoffset
  have hroot (z : ℂ) : sourceStandardRoot hp hp1 ψ n z = normalizedStandardRoot τ q z := by
    simp only [sourceStandardRoot,τ,q,sourcePeriodicGapDisplacement_apply]
  have hF : AnalyticOnNhd ℂ F (closedBall c R) := fun z hz =>
    (analyticAt_id.add analyticAt_const).mul (hE z hz)
  have hden : ∀ z ∈ sphere c R, τ ≠ z ∧ normalizedStandardRoot τ q z ≠ 0 ∧
      τ-z+normalizedStandardRoot τ q z ≠ 0 := by
    intro z hz
    have hτ : τ ≠ z := fun he => hcircle hz n (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
    refine ⟨hτ,?_,normalizedStandardRoot_add_ne_zero τ q z hτ⟩
    rw [← hroot]
    exact sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hcircle hz n)
  have hK : CircleIntegrable (fun z => normalizedActionCircleKernel τ q B z*F z) c R := by
    apply ContinuousOn.circleIntegrable hR
    intro z hz
    have ha : AnalyticAt ℂ (normalizedStandardRoot τ q) z := by
      have he : normalizedStandardRoot τ q = sourceStandardRoot hp hp1 ψ n := funext (fun w => (hroot w).symm)
      rw [he]
      exact sourceStandardRoot_analyticAt hp hp1 ψ n z (hcircle hz n)
    exact ((normalizedActionCircleKernel_analyticAt τ q B z ha (hden z hz).2.1
      (hden z hz).2.2).mul (hF z (sphere_subset_closedBall hz))).continuousAt.continuousWithinAt
  have hfactor := normalizedActionCircle_integral_factor τ q B c R F hR hF hK hden
  rw [sourceHigherActionCircle_one_eq_recentered hp hp1 ψ c R hR hcircle hzero b]
  have he : (∮ z in C(c,R), (z^2-b^2)*sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      ∮ z in C(c,R), -((τ+q*B-z)^2/normalizedStandardRoot τ q z)*F z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    have hf := sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ n z (hcircle hz)
    change sourceCriticalRootRatioJoint hp hp1 (z,ψ) = ((b-z)/sourceStandardRoot hp hp1 ψ n z)*E z at hf
    dsimp only
    rw [hf,hroot]
    dsimp [F]
    rw [hb]
    ring
  rw [he]
  change _ = q/2*normalizedActionCircleQuotient τ q B c R F
  calc
    _ = ((Real.pi : ℂ)⁻¹*(∮ z in C(c,R), -((τ+q*B-z)^2/normalizedStandardRoot τ q z)*F z))/2 := by ring
    _ = _ := by rw [hfactor]; ring

end NLS.ZakharovShabat
