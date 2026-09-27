import NLS.ZakharovShabat.SourcePsiNearFreeComplexUniformEquation
import NLS.ZakharovShabat.SourcePsiContourAnalytic

/-!
# Scalar psi contours at complex source parameters

The joint analytic contour integrand gives parameter holomorphy at
every complex source where the chosen fixed circle stays in its
canonical-root domain.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A fixed psi equation coordinate is Fréchet-holomorphic at any
complex parameter point whose contour lies in the common domain of
the jointly analytic integrand. -/
theorem differentiableAt_sourcePsiEquationCoordinate_of_contour_domain
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hD : IsOpen (sourcePsiContourJointDomain hp hp1 W))
    (hF : AnalyticOnNhd ℂ
      (sourcePsiContourIntegrandJoint hp hp1 n)
      (sourcePsiContourJointDomain hp hp1 W))
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    DifferentiableAt ℂ
      (fun b : Coeff p × CoeffPair p =>
        sourcePsiEquationCoordinate hp hp1 n m b.1 b.2 c R)
      (a,ψ) := by
  let D := sourcePsiContourJointDomain hp hp1 W
  let F := sourcePsiContourIntegrandJoint hp hp1 n
  have hbase (z : ℂ) (hz : z ∈ sphere c R) : (z,(a,ψ)) ∈ D :=
    ⟨hψW,hcircle hz⟩
  obtain ⟨V,hVopen,hbaseV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hD hF c R (a,ψ) hbase
  have hdiff :=
    NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
      F D hD hF c R hR V hVopen (a,ψ) hbaseV M
      (fun q hq θ =>
        (hbound (circleMap c R θ) (circleMap_mem_sphere c hR θ) q hq).1)
      (fun q hq θ =>
        (hbound (circleMap c R θ) (circleMap_mem_sphere c hR θ) q hq).2)
  have hcontour : DifferentiableAt ℂ
      (fun b : Coeff p × CoeffPair p =>
        sourcePsiContour hp hp1 n b.1 b.2 c R) (a,ψ) := by
    change DifferentiableAt ℂ
      (fun q : Coeff p × CoeffPair p =>
        (2*Real.pi : ℂ)⁻¹ * ∮ z in C(c,R), F (z,q)) (a,ψ)
    exact hdiff.const_mul _
  change DifferentiableAt ℂ
    (fun b : Coeff p × CoeffPair p =>
      (((n-m : ℤ) : ℂ) * (2*Real.pi : ℂ)) *
        sourcePsiContour hp hp1 n b.1 b.2 c R) (a,ψ)
  exact hcontour.const_mul _

end NLS.ZakharovShabat
