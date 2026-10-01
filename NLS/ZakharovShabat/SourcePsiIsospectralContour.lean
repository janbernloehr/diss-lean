import NLS.ZakharovShabat.SourceIsospectralDirection
import NLS.ZakharovShabat.SourcePsiComplexContourAnalytic

/-! # Isospectral variation of the actual psi contour equations

With the numerator-root input fixed, every actual psi contour integrand
has zero variation in an isospectral source direction. Differentiation
under the actual fixed circle proves the same for the scalar equations.
Their coordinate realization then gives zero source variation of the
entire selected Banach-valued equation.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Only the actual canonical-root denominator varies when the
numerator-root input is fixed. Isospectrality makes that variation zero. -/
theorem fderiv_sourcePsiContourIntegrand_isospectral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (h : CoeffPair p)
    (hiso : SourceIsospectralDirection hp φ h)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))) φ) h = 0 := by
  obtain ⟨W,_,_,hWreal,_,hroot⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  have hQ : DifferentiableAt ℂ (fun ψ : CoeffPair p => sourceCanonicalRoot hp hp1 ψ z) φ := by
    simpa only [Function.comp_def] using! ((hroot (z,φ) ⟨hWreal hreal,hz⟩).comp
      (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hne := sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz
  have hd := ((hasFDerivAt_inv hne).comp φ hQ.hasFDerivAt).const_mul (sourcePsiCandidate n (z,a))
  simp only [Function.comp_def] at hd
  simp only [sourcePsiContourIntegrandJoint,div_eq_mul_inv]
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply]
  rw [fderiv_sourceCanonicalRoot_eq_zero_of_isospectralDirection hp hp1 φ hreal h hiso z hz]
  simp

/-- Actual fixed-circle psi equations have zero source variation
in every isospectral direction, with the numerator roots held fixed. -/
theorem fderiv_sourcePsiEquationCoordinate_isospectral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (h : CoeffPair p)
    (hiso : SourceIsospectralDirection hp φ h) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourcePsiEquationCoordinate hp hp1 n m a ψ c R) φ) h = 0 := by
  obtain ⟨W,_,_,hWreal,hdata⟩ := exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let F := sourcePsiContourIntegrandJoint hp hp1 n
  let D := sourcePsiContourJointDomain hp hp1 W
  have hbase (z : ℂ) (hz : z ∈ sphere c R) : (z,(a,φ)) ∈ D := ⟨hWreal hreal,hcircle hz⟩
  obtain ⟨V,hVopen,hbaseV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle F D
      (hdata n).1 (hdata n).2 c R (a,φ) hbase
  let J : Coeff p × CoeffPair p → ℂ := fun q => ∮ z in C(c,R), F (z,q)
  have hdom : ∀ q ∈ V, ∀ θ : ℝ, (circleMap c R θ,q) ∈ D :=
    fun q hq θ => (hbound _ (circleMap_mem_sphere c hR θ) q hq).1
  have hdbound : ∀ q ∈ V, ∀ θ : ℝ, ‖fderiv ℂ F (circleMap c R θ,q)‖ ≤ M :=
    fun q hq θ => (hbound _ (circleMap_mem_sphere c hR θ) q hq).2
  have hJ := NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic F D
    (hdata n).1 (hdata n).2 c R hR V hVopen (a,φ) hbaseV M hdom hdbound
  have hsource := hJ.hasFDerivAt.comp φ (hasFDerivAt_prodMk_right a φ)
  simp only [Function.comp_def] at hsource
  have hformula := NLS.ComplexAnalysis.fderiv_circleIntegral_apply_of_jointAnalytic F D
    (hdata n).1 (hdata n).2 c R hR V hVopen (a,φ) hbaseV M hdom hdbound (0,h)
  have hzero : (∮ z in C(c,R),
      (fderiv ℂ (fun q : Coeff p × CoeffPair p => F (z,q)) (a,φ)) (0,h)) = 0 := by
    calc
      _ = ∮ z in C(c,R), (0 : ℂ) := by
        apply circleIntegral.integral_congr hR
        intro z hz
        dsimp only
        have hF := (((hdata n).2 (z,(a,φ)) (hbase z hz)).comp
          (f := fun q : Coeff p × CoeffPair p => (z,q)) (analyticAt_const.prod analyticAt_id)).differentiableAt
        have hpartial := (hF.hasFDerivAt.comp φ (hasFDerivAt_prodMk_right a φ)).fderiv
        simp only [Function.comp_def] at hpartial
        have heval := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hpartial
        simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] at heval
        exact heval.symm.trans
          (fderiv_sourcePsiContourIntegrand_isospectral_eq_zero hp hp1 n a φ hreal h hiso z (hcircle hz))
      _ = 0 := by simp [circleIntegral]
  have hJzero : (fderiv ℂ (fun ψ : CoeffPair p => J (a,ψ)) φ) h = 0 := by
    rw [hsource.fderiv]
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using hformula.trans hzero
  have heq : (fun ψ : CoeffPair p => sourcePsiEquationCoordinate hp hp1 n m a ψ c R) =
      (fun ψ : CoeffPair p => ((n-m : ℤ) : ℂ)*J (a,ψ)) := by
    funext ψ
    exact sourcePsiEquationCoordinate_eq_raw_circleIntegral hp hp1 n m a ψ c R
  rw [heq,fderiv_const_mul hsource.differentiableAt]
  simp only [smul_apply,smul_eq_mul]
  rw [hJzero,mul_zero]

/-- The full selected equation has zero source partial derivative
in an isospectral direction on any actual fixed contour chart. -/
theorem fderiv_sourcePsiSelectedEquation_isospectral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (h : CoeffPair p)
    (hiso : SourceIsospectralDirection hp φ h) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p)) (hUopen : IsOpen U) (hbase : (a,φ) ∈ U)
    (hcoord : ∀ q ∈ U, ∀ m : ℤ, (sourcePsiSelectedEquationSequence hp hp1 n c R q.1 q.2 : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (q.1 : Coeff p) q.2 (c m) (R m))
    (hF : DifferentiableAt ℂ (fun q : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c R q.1 q.2) (a,φ))
    (hcircle : ∀ m : ℤ, 0 ≤ R m ∧ sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    (fderiv ℂ (fun q : DeletedCoeff p n × CoeffPair p =>
      sourcePsiSelectedEquationSequence hp hp1 n c R q.1 q.2) (a,φ)) (0,h) = 0 := by
  let F := fun q : DeletedCoeff p n × CoeffPair p => sourcePsiSelectedEquationSequence hp hp1 n c R q.1 q.2
  have hsource := hF.hasFDerivAt.comp φ (hasFDerivAt_prodMk_right a φ)
  apply Subtype.ext
  ext m
  let E : DeletedCoeff p n →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  have heval := (E.hasFDerivAt.comp φ hsource).fderiv
  simp only [Function.comp_def] at heval
  have heq : (fun ψ : CoeffPair p => E (F (a,ψ))) =ᶠ[𝓝 φ]
      (fun ψ => sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ (c m) (R m)) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hUopen.mem_nhds hbase)] with ψ hψ
    exact hcoord (a,ψ) hψ m
  have hzero := fderiv_sourcePsiEquationCoordinate_isospectral_eq_zero hp hp1 n m (a : Coeff p)
    φ hreal h hiso (c m) (R m) (hcircle m).1 (hcircle m).2
  rw [← heq.fderiv_eq,heval] at hzero
  change E ((fderiv ℂ F (a,φ)) (0,h)) = E 0
  rw [map_zero]
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using hzero

end NLS.ZakharovShabat
