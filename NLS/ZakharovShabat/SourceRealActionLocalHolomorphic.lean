import NLS.ZakharovShabat.SourceRealActionEnclosingCircle
import NLS.ZakharovShabat.SourceActionCircleAnalytic

/-!
# Local holomorphic circle action through a real indexed action

At each real-type source, an explicit midpoint circle represents the
indexed real action. Joint analyticity of the weighted root quotient
then makes the action on this fixed circle complex differentiable on
a source neighborhood and analytic along every complex affine line.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every indexed real action is the value at its base source of a
locally complex-differentiable fixed-circle action. -/
theorem exists_local_differentiable_circle_through_sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        sourceRealAction hp hp1 φ hreal n =
          sourceActionCircle hp hp1 φ c R ∧
        DifferentiableOn ℂ
          (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c R) V := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,hdisc⟩ :=
    exists_source_midpoint_closedBall_subset_omittedDomain
      hp hp1 φ hreal n
  let η : ℝ := ε/2
  have hη : η ∈ Ioc 0 ε := by
    dsimp [η]
    constructor <;> linarith
  let R : ℝ := d+η
  have hd : 0 ≤ d := by
    have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 n)
    dsimp [d]
    linarith
  have hR : 0 < R := by dsimp [R]; linarith [hη.1]
  have hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 φ n := hdisc η hη
  have hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R :=
    sourcePeriodicSegment_subset_midpoint_ball
      hp hp1 φ hreal n η hη.1
  have hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ :=
    sourceCanonicalRootDomain_of_enclosingCircle
      hp hp1 φ n c R hseg hother
  have hvalue : sourceRealAction hp hp1 φ hreal n =
      sourceActionCircle hp hp1 φ c R :=
    sourceRealAction_eq_enclosing_midpointCircle
      hp hp1 φ hreal n R (by change d < R; dsimp [R]; linarith [hη.1]) hother
  obtain ⟨W,_,_,hWreal,hDopen,hweighted⟩ :=
    exists_global_sourceActionIntegrand_jointAnalytic hp hp1
  have hbase (z : ℂ) (hz : z ∈ sphere c R) :
      (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
    ⟨hWreal hreal, hcircle hz⟩
  obtain ⟨V,hVopen,hφV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      (sourceActionIntegrandJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)
      hDopen hweighted c R φ hbase
  have hdiff : DifferentiableOn ℂ
      (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c R) V := by
    intro ψ hψ
    have hcircleDiff :=
      NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
        (sourceActionIntegrandJoint hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W)
        hDopen hweighted c R hR.le V hVopen ψ hψ M
        (fun b hb θ => (hbound (circleMap c R θ)
          (circleMap_mem_sphere c hR.le θ) b hb).1)
        (fun b hb θ => (hbound (circleMap c R θ)
          (circleMap_mem_sphere c hR.le θ) b hb).2)
    change DifferentiableWithinAt ℂ
      (fun b : CoeffPair p => (Real.pi : ℂ)⁻¹ *
        ∮ z in C(c,R), sourceActionIntegrandJoint hp hp1 (z,b)) V ψ
    exact (hcircleDiff.const_mul (Real.pi : ℂ)⁻¹).differentiableWithinAt
  exact ⟨c,R,hR,V,hVopen,hφV,hvalue,hdiff⟩

/-- Through the indexed real action, the fixed-circle action is
analytic along every complex affine source direction. -/
theorem exists_local_lineAnalytic_circle_through_sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourceRealAction hp hp1 φ hreal n =
        sourceActionCircle hp hp1 φ c R ∧
      ∀ h : CoeffPair p,
        AnalyticAt ℂ (fun t : ℂ =>
          sourceActionCircle hp hp1 (φ+t•h) c R) 0 := by
  obtain ⟨c,R,hR,V,hVopen,hφV,hvalue,hdiff⟩ :=
    exists_local_differentiable_circle_through_sourceRealAction
      hp hp1 φ hreal n
  refine ⟨c,R,hR,hvalue,?_⟩
  intro h
  let a : ℂ → CoeffPair p := fun t => φ+t•h
  have ha : Differentiable ℂ a := by
    dsimp [a]
    fun_prop
  let U : Set ℂ := a ⁻¹' V
  have hUopen : IsOpen U := hVopen.preimage ha.continuous
  have h0 : (0:ℂ) ∈ U := by simpa [U,a] using hφV
  have hline : DifferentiableOn ℂ
      (fun t : ℂ => sourceActionCircle hp hp1 (a t) c R) U := by
    intro t ht
    exact (((hdiff (a t) ht).differentiableAt (hVopen.mem_nhds ht)).comp t
      (ha t)).differentiableWithinAt
  exact hline.analyticAt (hUopen.mem_nhds h0)

end NLS.ZakharovShabat
