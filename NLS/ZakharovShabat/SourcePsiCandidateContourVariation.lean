import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation
import NLS.ZakharovShabat.SourcePsiContourAnalytic

/-!
# Root-direction variation of the psi contour integrand

The canonical spectral root depends on the potential but not on the
root-sequence parameter. Differentiating the contour integrand in a
root direction therefore places the entire numerator variation over
that fixed denominator, as in the first display of Lemma 12.7.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The root-direction derivative of the psi integrand is the entire
numerator variation divided by the canonical spectral root. -/
theorem fderiv_sourcePsiContourIntegrand_root_direction
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    (fderiv ℂ (fun b : Coeff p =>
      sourcePsiContourIntegrandJoint hp hp1 n (z,(b,ψ))) a) h =
      sourcePsiCandidateVariation n a h z /
        sourceCanonicalRoot hp hp1 ψ z := by
  have hnum : DifferentiableAt ℂ
      (fun b : Coeff p => sourcePsiCandidate n (z,b)) a := by
    exact ((analyticOnNhd_sourcePsiCandidate hp hp1 n
      (z,a) (Set.mem_univ _)).comp
        (f := fun b : Coeff p => (z,b))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  simp only [sourcePsiContourIntegrandJoint, div_eq_mul_inv]
  rw [fderiv_mul_const hnum]
  simp [sourcePsiCandidateVariation, smul_eq_mul, mul_comm]

/-- Near real-type data, the root-direction derivative of a fixed
scalar psi equation is the contour integral of the entire numerator
variation over the canonical spectral root. -/
theorem exists_local_sourcePsiEquationCoordinate_fderiv_root_direction
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : Metric.sphere c R ⊆
      sourceCanonicalRootDomain hp hp1 φ) :
    ∃ V : Set (Coeff p × CoeffPair p), IsOpen V ∧ (a,φ) ∈ V ∧
      ∀ b : Coeff p, ∀ ψ : CoeffPair p, (b,ψ) ∈ V →
      ∀ h : Coeff p,
        (fderiv ℂ (fun x : Coeff p =>
          sourcePsiEquationCoordinate hp hp1 n m x ψ c R) b) h =
          ((n-m : ℤ) : ℂ) *
            (∮ z in C(c,R),
              sourcePsiCandidateVariation n b h z /
                sourceCanonicalRoot hp hp1 ψ z) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let D := sourcePsiContourJointDomain hp hp1 W
  let F := sourcePsiContourIntegrandJoint hp hp1 n
  have hbase (z : ℂ) (hz : z ∈ Metric.sphere c R) : (z,(a,φ)) ∈ D :=
    ⟨hreal hφ,hcircle hz⟩
  obtain ⟨V,hVopen,hbaseV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D (hdata n).1 (hdata n).2 c R (a,φ) hbase
  refine ⟨V,hVopen,hbaseV,?_⟩
  intro b ψ hbψ h
  let J : Coeff p × CoeffPair p → ℂ :=
    fun q => ∮ z in C(c,R), F (z,q)
  have hdom : ∀ q ∈ V, ∀ θ : ℝ,
      (circleMap c R θ,q) ∈ D := by
    intro q hq θ
    exact (hbound (circleMap c R θ)
      (circleMap_mem_sphere c hR θ) q hq).1
  have hdbound : ∀ q ∈ V, ∀ θ : ℝ,
      ‖fderiv ℂ F (circleMap c R θ,q)‖ ≤ M := by
    intro q hq θ
    exact (hbound (circleMap c R θ)
      (circleMap_mem_sphere c hR θ) q hq).2
  have hJdiff : DifferentiableAt ℂ J (b,ψ) :=
    NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
      F D (hdata n).1 (hdata n).2 c R hR
        V hVopen (b,ψ) hbψ M hdom hdbound
  have hJroot : HasFDerivAt (fun x : Coeff p => J (x,ψ))
      ((fderiv ℂ J (b,ψ)).comp
        (ContinuousLinearMap.inl ℂ (Coeff p) (CoeffPair p))) b := by
    exact HasFDerivAt.comp b hJdiff.hasFDerivAt
      (hasFDerivAt_prodMk_left (𝕜 := ℂ) b ψ)
  have hJformula :=
    NLS.ComplexAnalysis.fderiv_circleIntegral_apply_of_jointAnalytic
      F D (hdata n).1 (hdata n).2 c R hR
        V hVopen (b,ψ) hbψ M hdom hdbound (h,0)
  have hintegrand (z : ℂ) (hz : z ∈ Metric.sphere c R) :
      (fderiv ℂ (fun q : Coeff p × CoeffPair p => F (z,q))
        (b,ψ)) (h,0) =
        sourcePsiCandidateVariation n b h z /
          sourceCanonicalRoot hp hp1 ψ z := by
    have hF : DifferentiableAt ℂ
        (fun q : Coeff p × CoeffPair p => F (z,q)) (b,ψ) := by
      exact (((hdata n).2 (z,(b,ψ))
        (hbound z hz (b,ψ) hbψ).1).comp
          (f := fun q : Coeff p × CoeffPair p => (z,q))
          (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hFroot : fderiv ℂ (fun x : Coeff p => F (z,(x,ψ))) b =
        (fderiv ℂ (fun q : Coeff p × CoeffPair p => F (z,q))
          (b,ψ)).comp
            (ContinuousLinearMap.inl ℂ (Coeff p) (CoeffPair p)) := by
      exact (HasFDerivAt.comp b hF.hasFDerivAt
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) b ψ)).fderiv
    rw [← fderiv_sourcePsiContourIntegrand_root_direction
      hp hp1 n b h ψ z]
    change (fderiv ℂ (fun q : Coeff p × CoeffPair p => F (z,q))
      (b,ψ)) (h,0) =
        (fderiv ℂ (fun x : Coeff p => F (z,(x,ψ))) b) h
    rw [hFroot]
    rfl
  have hcircleEq :
      (∮ z in C(c,R),
        (fderiv ℂ (fun q : Coeff p × CoeffPair p => F (z,q))
          (b,ψ)) (h,0)) =
      ∮ z in C(c,R),
        sourcePsiCandidateVariation n b h z /
          sourceCanonicalRoot hp hp1 ψ z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    exact hintegrand z hz
  have hJrootFormula :
      (fderiv ℂ (fun x : Coeff p => J (x,ψ)) b) h =
      ∮ z in C(c,R),
        sourcePsiCandidateVariation n b h z /
          sourceCanonicalRoot hp hp1 ψ z := by
    rw [hJroot.fderiv]
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using hJformula.trans hcircleEq
  have hEq : (fun x : Coeff p =>
      sourcePsiEquationCoordinate hp hp1 n m x ψ c R) =
      (fun x : Coeff p => ((n-m : ℤ) : ℂ) * J (x,ψ)) := by
    funext x
    exact sourcePsiEquationCoordinate_eq_raw_circleIntegral
      hp hp1 n m x ψ c R
  rw [hEq, fderiv_const_mul hJroot.differentiableAt]
  simp only [smul_apply, smul_eq_mul]
  rw [hJrootFormula]

end NLS.ZakharovShabat
