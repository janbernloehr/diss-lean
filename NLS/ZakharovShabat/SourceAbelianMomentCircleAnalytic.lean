import NLS.ZakharovShabat.SourceAbelianMomentCircle
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Analyticity of the Section 20 moments on a fixed contour

Joint analyticity of the actual primitive and the psi quotient gives
analytic moments in both the root-displacement and source parameters.
All moment orders, including zero, use the same open joint domain.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAbelianMomentIntegrand_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W U : Set (CoeffPair p)) (n k : ℤ) (m : ℕ)
    (hF : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W k)
      (sourceCanonicalRootJointDomain hp hp1 U))
    (hψ : AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
      (sourcePsiContourJointDomain hp hp1 U)) :
    AnalyticOnNhd ℂ (sourceAbelianMomentIntegrand hp hp1 W n k m)
      (sourcePsiContourJointDomain hp hp1 U) := by
  intro t ht
  have hproj : AnalyticAt ℂ (fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.2)) t :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  exact ((hF (t.1,t.2.2) ht).comp
    (f := fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.2)) hproj).pow m |>.mul (hψ t ht)

/-- The fixed-circle moment is analytic on any open parameter region
where the same circle stays inside the analytic joint domain. -/
theorem sourceAbelianMomentCircle_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W U : Set (CoeffPair p)) (n k : ℤ) (m : ℕ)
    (hD : IsOpen (sourcePsiContourJointDomain hp hp1 U))
    (hF : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W k)
      (sourceCanonicalRootJointDomain hp hp1 U))
    (hψ : AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
      (sourcePsiContourJointDomain hp hp1 U))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (V : Set (Coeff p × CoeffPair p)) (hV : IsOpen V)
    (hcircle : ∀ b ∈ V, ∀ z ∈ sphere c R, (z,b) ∈ sourcePsiContourJointDomain hp hp1 U) :
    AnalyticOnNhd ℂ (fun b : Coeff p × CoeffPair p =>
      sourceAbelianMomentCircle hp hp1 W n k m b.1 b.2 c R) V :=
  analyticOnNhd_circleIntegral_of_jointAnalytic _ hD
    (sourceAbelianMomentIntegrand_analyticOnNhd hp hp1 W U n k m hF hψ)
    c R hR hV hcircle

/-- Analyticity at a parameter point requires only that its circle
avoid the moving gaps: compactness supplies a common parameter neighborhood. -/
theorem analyticAt_sourceAbelianMomentCircle_of_contour_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W U : Set (CoeffPair p)) (n k : ℤ) (m : ℕ)
    (hD : IsOpen (sourcePsiContourJointDomain hp hp1 U))
    (hF : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W k)
      (sourceCanonicalRootJointDomain hp hp1 U))
    (hψ : AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
      (sourcePsiContourJointDomain hp hp1 U))
    (a : Coeff p) (ψ : CoeffPair p) (hψU : ψ ∈ U)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    AnalyticAt ℂ (fun b : Coeff p × CoeffPair p =>
      sourceAbelianMomentCircle hp hp1 W n k m b.1 b.2 c R) (a,ψ) := by
  have hbase (z : ℂ) (hz : z ∈ sphere c R) :
      (z,(a,ψ)) ∈ sourcePsiContourJointDomain hp hp1 U := ⟨hψU,hcircle hz⟩
  obtain ⟨V,hV,hbaseV,_,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle
    _ _ hD (sourceAbelianMomentIntegrand_analyticOnNhd hp hp1 W U n k m hF hψ)
    c R (a,ψ) hbase
  exact sourceAbelianMomentCircle_analyticOnNhd hp hp1 W U n k m hD hF hψ
    c R hR V hV (fun b hb z hz => (hbound z hz b hb).1) (a,ψ) hbaseV

/-- Fixed-contour moments along the actual normalized psi branch are
analytic in the source, including its omitted-index period. -/
theorem SourcePsiNormalizedComplexExtension.analyticAt_momentCircle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (W U : Set (CoeffPair p)) (n k : ℤ) (m : ℕ)
    (hD : IsOpen (sourcePsiContourJointDomain hp hp1 U))
    (hF : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W k)
      (sourceCanonicalRootJointDomain hp hp1 U))
    (hψ : AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
      (sourcePsiContourJointDomain hp hp1 U))
    (ψ : CoeffPair p) (hψV : ψ ∈ V) (hψU : ψ ∈ U)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    AnalyticAt ℂ (fun χ => sourceAbelianMomentCircle hp hp1 W n k m
      (s n χ : Coeff p) χ c R) ψ := by
  have hbranch : AnalyticAt ℂ (fun χ => (s n χ : Coeff p)) ψ :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.analyticAt (s n ψ)).comp
      (hs.analytic n ψ hψV)
  exact (analyticAt_sourceAbelianMomentCircle_of_contour_domain hp hp1 W U n k m
    hD hF hψ (s n ψ : Coeff p) ψ hψU c R hR hcircle).comp
      (f := fun χ => ((s n χ : Coeff p),χ)) (hbranch.prod analyticAt_id)

end NLS.ZakharovShabat
