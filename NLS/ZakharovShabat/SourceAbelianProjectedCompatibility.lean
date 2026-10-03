import NLS.ZakharovShabat.SourceAbelianProjectedPrimitive

/-! # Agreement of the projected primitive with all previous charts

The source path from a potential's real projection stays in the new
domain and in every real-centered chart that contains the endpoint.
The projected primitive and the old chart have a common exponential
and equal initial values along this path, hence equal terminal values.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceRealProjectionPath (hp : p ≠ ⊤) (ψ : CoeffPair p) (s : ℝ) : CoeffPair p :=
  (sourceRealTypeProjection hp ψ).val+s • (ψ-(sourceRealTypeProjection hp ψ).val)

@[simp] theorem sourceRealProjectionPath_zero (hp : p ≠ ⊤) (ψ : CoeffPair p) :
    sourceRealProjectionPath hp ψ 0 = (sourceRealTypeProjection hp ψ).val := by simp [sourceRealProjectionPath]

@[simp] theorem sourceRealProjectionPath_one (hp : p ≠ ⊤) (ψ : CoeffPair p) :
    sourceRealProjectionPath hp ψ 1 = ψ := by simp [sourceRealProjectionPath]

theorem sourceRealTypeProjection_path (hp : p ≠ ⊤) (ψ : CoeffPair p) (s : ℝ) :
    sourceRealTypeProjection hp (sourceRealProjectionPath hp ψ s) = sourceRealTypeProjection hp ψ := by
  simp only [sourceRealProjectionPath,map_add,map_smul,map_sub,sourceRealTypeProjection_subtype,
    sub_self,smul_zero,add_zero]

/-- Every initial subsegment of the projection path remains in the
projected domain. The real projection is unchanged along the path. -/
theorem sourceRealProjectionPath_mem_projectedDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (z : ℂ) (ψ : CoeffPair p) (ht : (z,ψ) ∈ sourceAbelianProjectedDomain hp hp1 W)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    (z,sourceRealProjectionPath hp ψ s) ∈ sourceAbelianProjectedDomain hp hp1 W := by
  intro r hr
  have hrs : r*s ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg hr.1 hs.1,by nlinarith [hr.1,hr.2,hs.1,hs.2]⟩
  have h := ht (r*s) hrs
  change sourceSegmentMap (sourceRealTypeProjection hp (sourceRealProjectionPath hp ψ s)).val
    ((r : ℂ),(z,sourceRealProjectionPath hp ψ s)) ∈ _
  rw [sourceRealTypeProjection_path]
  change (z,(sourceRealTypeProjection hp ψ).val+r •
    (sourceRealProjectionPath hp ψ s-(sourceRealTypeProjection hp ψ).val)) ∈ _
  simp only [sourceRealProjectionPath,add_sub_cancel_left,smul_smul]
  simpa only [sourceAbelianProjectionAnchor,sourceSegmentMap,Complex.coe_smul] using! h

/-- Every existing product chart gives the same values as the
projection-normalized construction at all common complex-source points. -/
theorem sourceAbelianProjectedPrimitive_eq_chart
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (D : SourceAbelianJointChart hp hp1) (n : ℤ) (t : ℂ × CoeffPair p)
    (ht : t ∈ sourceAbelianProjectedDomain hp hp1 W) (hchart : t ∈ D.domain) :
    sourceAbelianProjectedPrimitive hp hp1 n t = D.toFun n t := by
  let L : ℝ → ℂ × CoeffPair p := fun s => (t.1,sourceRealProjectionPath hp t.2 s)
  have hL : Continuous L := by dsimp [L,sourceRealProjectionPath]; fun_prop
  have hLp (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : L s ∈ sourceAbelianProjectedDomain hp hp1 W :=
    sourceRealProjectionPath_mem_projectedDomain hp hp1 W t.1 t.2 ht s hs
  have hLc (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : L s ∈ D.domain := by
    have h := sourceSegmentMap_mem (Metric.ball D.center D.radius) (Metric.ball D.source.val D.radius)
      (sourceRealTypeProjection hp t.2).val (convex_ball _ _) (D.real_projection_mem t hchart).2 t hchart s hs
    simpa only [SourceAbelianJointChart.domain,sourceSegmentMap,Complex.coe_smul,L,sourceRealProjectionPath] using! h
  have hF : ContinuousOn (fun s => sourceAbelianProjectedPrimitive hp hp1 n (L s)) (Icc (0:ℝ) 1) :=
    (show ContinuousOn (sourceAbelianProjectedPrimitive hp hp1 n) (sourceAbelianProjectedDomain hp hp1 W) from
      fun u hu => (continuousAt_sourceAbelianProjectedPrimitive hp hp1 W hD hM n u hu).continuousWithinAt).comp hL.continuousOn hLp
  have hG : ContinuousOn (fun s => D.toFun n (L s)) (Icc (0:ℝ) 1) :=
    (D.analytic n).continuousOn.comp hL.continuousOn hLc
  have he := continuousLogarithms_eqOn (fun s => sourceAbelianProjectedPrimitive hp hp1 n (L s))
    (fun s => D.toFun n (L s)) (Icc (0:ℝ) 1) isPreconnected_Icc hF hG
    (fun s hs => (sourceAbelianProjectedPrimitive_exp hp hp1 W hM n (L s) (hLp s hs)).trans
      (sourceAbelianLogChart_exp hp hp1 D.source.val D.source.property D.center n (L s)
        (D.root_domain (D.center,D.source.val) D.center_mem) (D.root_domain (L s) (hLc s hs))).symm)
    0 (by simp) (by
      simp only [L,sourceRealProjectionPath_zero,sourceAbelianProjectedPrimitive_eq_real]
      exact (D.real_eq n (sourceRealTypeProjection hp t.2) (D.real_projection_mem t hchart).2 t.1 hchart.1).symm)
  simpa only [L,sourceRealProjectionPath_one] using he (show (1:ℝ) ∈ Icc 0 1 by simp)

/-- The projected primitive is an exact continuation of the old glued
function on their entire common open domain. -/
theorem sourceAbelianProjectedPrimitive_eq_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : EqOn (sourceAbelianProjectedPrimitive hp hp1 n) (sourceAbelianJointPrimitive hp hp1 n)
      (sourceAbelianProjectedDomain hp hp1 W ∩ sourceAbelianJointDomain hp hp1) := by
  intro t ht
  obtain ⟨D,hchart⟩ := mem_iUnion.mp ht.2
  exact (sourceAbelianProjectedPrimitive_eq_chart hp hp1 W hD hM D n t ht.1 hchart).trans
    (sourceAbelianJointPrimitive_eq_chart hp hp1 n D hchart).symm

end NLS.ZakharovShabat
