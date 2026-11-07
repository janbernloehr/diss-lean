import NLS.ZakharovShabat.SourceHigherActionOneKernel
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedCircleValue
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic

/-! # Analytic filled quotients for the original level-two contour

An actual original isolating circle is retained on a complex source
neighborhood. The weighted rationalized contour is analytic there and
factors the original indexed higher action, including complex collapsed
gaps. At collapse its value is midpoint times the ordinary collapsed
normalized action. The spectral weight is never replaced by a mean value.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceHigherActionOneCircleQuotient_eq_kernel
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℂ) (R : ℝ) (ψ : CoeffPair p) :
    sourceHigherActionOneCircleQuotient hp hp1 n c R ψ =
      normalizedActionCircleQuotient
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)
        ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2)
        (canonicalCriticalGapQuotient hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n) c R
        (fun z => (z+canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)*
          sourceCriticalRootRatioExtension hp hp1 n ψ z)/2 := by
  unfold sourceHigherActionOneCircleQuotient normalizedActionCircleQuotient
  have he : (fun z => sourceHigherActionOneKernelJoint hp hp1 n (z,ψ)) =
      fun z => normalizedActionCircleKernel
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)
        ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2)
        (canonicalCriticalGapQuotient hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n) z*
        ((z+canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)*
          sourceCriticalRootRatioExtension hp hp1 n ψ z) := by
    funext z
    unfold sourceHigherActionOneKernelJoint sourceNormalizedActionCircleIntegrandJoint
    ring
  rw [he]
  ring

theorem sourceHigherActionOneCircleQuotient_collapsed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0)
    (hcrit : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n =
      sourceStandardRootMidpoint hp hp1 ψ n)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hE : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R)) :
    sourceHigherActionOneCircleQuotient hp hp1 n c R ψ =
      sourceStandardRootMidpoint hp hp1 ψ n*sourceNormalizedActionCollapsedCandidate hp hp1 n ψ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let B := canonicalCriticalGapQuotient hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  have hτ : τ ∈ ball c R := hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hweighted : AnalyticOnNhd ℂ (fun z => (z+τ)*E z) (closedBall c R) :=
    fun z hz => (analyticAt_id.add analyticAt_const).mul (hE z hz)
  have he := normalizedActionCircleQuotient_zeroGap τ B c R (fun z => (z+τ)*E z) hR hτ hweighted
  rw [sourceHigherActionOneCircleQuotient_eq_kernel,hgap,zero_pow (by norm_num : (2:ℕ) ≠ 0),hcrit]
  change normalizedActionCircleQuotient τ 0 B c R (fun z => (z+τ)*E z)/2 = _
  rw [he]
  unfold sourceNormalizedActionCollapsedCandidate
  change I*((τ+τ)*E τ)/4/2 = τ*(I*E τ/4)
  ring

theorem exists_local_sourceHigherActionOneCircleQuotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        AnalyticOnNhd ℂ (sourceHigherActionOneCircleQuotient hp hp1 n c R) U ∧
        ∀ ψ ∈ U,
          sourceIndexedHigherAction hp hp1 n 1 ψ =
            (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*sourceHigherActionOneCircleQuotient hp hp1 n c R ψ ∧
          (sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
            sourceHigherActionOneCircleQuotient hp hp1 n c R ψ =
              sourceStandardRootMidpoint hp hp1 ψ n*sourceNormalizedActionCollapsedCandidate hp hp1 n ψ) := by
  obtain ⟨N,ε,_,_,V₀,hV₀,_,hφV₀,d,hD⟩ :=
    exists_local_source_quantitative_isolating_discs hp hp1 φ hφ
  obtain ⟨a,R,hR,ha⟩ := hD.discs n
  let c : ℂ := a
  have hgeom : ∀ ψ ∈ V₀, sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    intro ψ hψ
    let D := hD.periodCircle ψ hψ n a R hR ha
    exact ⟨D.gap,D.closedBall_subset_omittedDomain⟩
  obtain ⟨V₁,hV₁,hφV₁,hsub,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_on_givenCircle
      hp hp1 φ hφ n V₀ hV₀ hφV₀ c R hR hgeom
  let F := sourceHigherActionOneKernelJoint hp hp1 n
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hDopen : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  have hcircle : ∀ z ∈ sphere c R, (z,φ) ∈ D := by
    intro z hz
    exact analyticAt_sourceHigherActionOneKernelJoint_of_realType hp hp1 n φ hφ z
      (sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n c R
        (hgeom φ hφV₀).1 (hgeom φ hφV₀).2 hz)
  obtain ⟨V₂,hV₂,hφV₂,M,_,hbound⟩ :=
    exists_uniform_joint_fderiv_bound_on_circle F D hDopen hF c R φ hcircle
  obtain ⟨W₁,hW₁,hreal₁,hEdata⟩ := exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  obtain ⟨W₂,hW₂,_,hreal₂,hexact⟩ := exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  let U := ((V₁ ∩ V₂) ∩ W₁) ∩ W₂
  have hU : IsOpen U := ((hV₁.inter hV₂).inter hW₁).inter hW₂
  have hφU : φ ∈ U := ⟨⟨⟨hφV₁,hφV₂⟩,hreal₁ hφ⟩,hreal₂ hφ⟩
  refine ⟨U,hU,hφU,c,R,hR,?_,?_⟩
  · apply analyticOnNhd_of_complexDifferentiableOn _ U hU
    intro ψ hψ
    have hd := differentiableAt_circleIntegral_of_jointAnalytic F D hDopen hF c R hR.le U hU ψ hψ M
      (fun b hb θ => (hbound (circleMap c R θ) (circleMap_mem_sphere c hR.le θ) b hb.1.1.2).1)
      (fun b hb θ => (hbound (circleMap c R θ) (circleMap_mem_sphere c hR.le θ) b hb.1.1.2).2)
    exact (hd.const_mul (-(2*(Real.pi : ℂ))⁻¹)).differentiableWithinAt
  · intro ψ hψ
    have hψ₀ := hsub hψ.1.1.1
    have hgeometry := hgeom ψ hψ₀
    have hE : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R) :=
      fun z hz => hEdata ψ hψ.1.2 n z (hgeometry.2 hz)
    have hoff := (hexact ψ hψ.2 n).2
    let B := canonicalCriticalGapQuotient hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n
    have hoff' : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*B := by
      simpa only [sourcePeriodicGapDisplacement_apply,B] using hoff
    refine ⟨?_,?_⟩
    · rw [sourceIndexedHigherAction_eq_circle (hD.periodCircle ψ hψ₀ n a R hR ha) 1]
      have he := sourceHigherActionCircle_one_eq_squaredGap_mul_kernel hp hp1 ψ n c R B hR.le
        (sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hgeometry.1 hgeometry.2)
        (hzero ψ hψ.1.1.1) hE hoff'
      rw [sourceHigherActionOneCircleQuotient_eq_kernel]
      exact he.trans (by ring)
    · intro hgap
      have hcrit : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n =
          sourceStandardRootMidpoint hp hp1 ψ n := by
        rw [hgap,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul] at hoff'
        exact sub_eq_zero.mp hoff'
      exact sourceHigherActionOneCircleQuotient_collapsed hp hp1 ψ n c R hR hgap hcrit hgeometry.1 hE

end NLS.ZakharovShabat
