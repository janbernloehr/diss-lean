import NLS.ZakharovShabat.SourceActionCircle
import NLS.ZakharovShabat.SourceCriticalRootRatioCircleDerivativeBound
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-!
# Source differentiability of a fixed-circle action

For a real-type base source, one isolating circle works for nearby
complex sources. The weighted critical-root quotient is jointly
analytic on that circle, and compactness bounds its joint derivative.
Differentiation under the circle integral makes the corresponding
action complex Fréchet differentiable in the source parameter.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integrand of the action circle, jointly in the spectral and
source parameters. -/
def sourceActionIntegrandJoint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ℂ × CoeffPair p → ℂ :=
  fun t => t.1 * sourceCriticalRootRatioJoint hp hp1 t

/-- On the common moving-gap complement, the weighted integrand is
jointly analytic. -/
theorem exists_global_sourceActionIntegrand_jointAnalytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceActionIntegrandJoint hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W) := by
  obtain ⟨W,hWopen,hWconn,hreal,hDopen,hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  refine ⟨W,hWopen,hWconn,hreal,hDopen,?_⟩
  intro t ht
  exact analyticAt_fst.mul (hquot t ht)

/-- Around each real-type source and gap index, the fixed-circle
action is complex differentiable throughout a source neighborhood. -/
theorem exists_local_sourceActionCircle_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        DifferentiableOn ℂ (fun ψ : CoeffPair p =>
          sourceActionCircle hp hp1 ψ c R) V := by
  obtain ⟨W,_,_,hreal,hDopen,hweighted⟩ :=
    exists_global_sourceActionIntegrand_jointAnalytic hp hp1
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle
      hp hp1 φ hφ n
  have hcircle (z : ℂ) (hz : z ∈ sphere c R) :
      (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
    ⟨hreal hφ,(hgeom φ hφV₀).2.2 hz⟩
  obtain ⟨V₁,hV₁open,hφV₁,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      (sourceActionIntegrandJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)
      hDopen hweighted c R φ hcircle
  let V := V₀ ∩ V₁
  have hVopen : IsOpen V := hV₀open.inter hV₁open
  have hφV : φ ∈ V := ⟨hφV₀,hφV₁⟩
  refine ⟨V,hVopen,hφV,c,R,hR,?_,?_⟩
  · intro ψ hψ
    obtain ⟨hseg,hother,_⟩ := hgeom ψ hψ.1
    exact ⟨hseg,hother⟩
  · intro ψ hψ
    have hdiff :=
      NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
        (sourceActionIntegrandJoint hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W)
        hDopen hweighted c R hR.le V hVopen ψ hψ M
        (fun b hb θ => (hbound (circleMap c R θ)
          (circleMap_mem_sphere c hR.le θ) b hb.2).1)
        (fun b hb θ => (hbound (circleMap c R θ)
          (circleMap_mem_sphere c hR.le θ) b hb.2).2)
    change DifferentiableWithinAt ℂ
      (fun b : CoeffPair p => (Real.pi : ℂ)⁻¹ *
        ∮ z in C(c,R), sourceActionIntegrandJoint hp hp1 (z,b)) V ψ
    exact (hdiff.const_mul (Real.pi : ℂ)⁻¹).differentiableWithinAt

/-- Every complex affine line through a real-type source sees an
analytic fixed-circle action near that source. -/
theorem exists_sourceActionCircle_lineAnalyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∀ h : CoeffPair p,
        AnalyticAt ℂ (fun t : ℂ =>
          sourceActionCircle hp hp1 (φ+t•h) c R) 0 := by
  obtain ⟨V,hVopen,hφV,c,R,hR,_,hdiff⟩ :=
    exists_local_sourceActionCircle_differentiableOn hp hp1 φ hφ n
  refine ⟨c,R,hR,?_⟩
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
