import NLS.ZakharovShabat.SourceActionChiCosine
import NLS.ZakharovShabat.SourceNormalizedActionCircleAnalytic
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-!
# The rationalized action kernel on the original common domain

The original symmetric endpoint and critical-offset data give joint
analyticity at every complex source. The kernel has no gap denominator,
so fixed-circle candidates remain analytic through every collapsed gap.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Joint regularity of the earlier deleted extension on the same omitted domain. -/
theorem SourceEquation2_18Data.criticalRatioExtension_joint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceCriticalRootRatioExtension hp hp1 n t.2 t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 W n) := by
  intro t ht
  apply (analyticAt_const.mul (H.joint n t ht)).congr
  filter_upwards [(H.criticalOffsets.previous.previous.previous.roots.joint n).1.mem_nhds ht] with q hq
  exact (sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 q.2 n q.1 hq.2).symm

/-- The actual rationalized kernel is jointly analytic off all moving gaps in W. -/
theorem SourceEquation2_18Data.normalizedKernel_joint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceNormalizedActionCircleIntegrandJoint hp hp1 n)
      (sourceCanonicalRootJointDomain hp hp1 W) := by
  intro x hx
  let τ (ψ : CoeffPair p) := canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let q (ψ : CoeffPair p) := (sourcePeriodicGapDisplacement hp hp1 ψ n)^2
  let B (ψ : CoeffPair p) := canonicalCriticalGapQuotient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let w (t : ℂ × CoeffPair p) := sourceStandardRoot hp hp1 t.2 n t.1
  have h2 := H.criticalOffsets.previous.previous.previous.roots.roots.symmetric
  have hτ : AnalyticAt ℂ τ x.2 := h2.midpoint n x.2 hx.1
  have hq : AnalyticAt ℂ q x.2 := by
    simpa only [q,sourcePeriodicGapDisplacement_apply] using h2.squared_gap n x.2 hx.1
  have hB : AnalyticAt ℂ B x.2 := by
    simpa only [sourceCriticalGapQuotient_apply] using H.criticalOffsets.analytic n x.2 hx.1
  have hτj := hτ.comp (f := fun t : ℂ × CoeffPair p => t.2) (analyticAt_snd (p := x))
  have hqj := hq.comp (f := fun t : ℂ × CoeffPair p => t.2) (analyticAt_snd (p := x))
  have hBj := hB.comp (f := fun t : ℂ × CoeffPair p => t.2) (analyticAt_snd (p := x))
  have hw : AnalyticAt ℂ w x := h2.standardRoot_joint n x ⟨hx.1,hx.2 n⟩
  have hwne : w x ≠ 0 := sourceStandardRoot_ne_zero_off_segment hp hp1 x.2 n x.1 (hx.2 n)
  have hτne : τ x.2 ≠ x.1 := by
    intro he
    exact hx.2 n (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 x.2 n)
  have hplus : τ x.2-x.1+w x ≠ 0 := by
    simpa only [τ,q,w,sourceStandardRoot,sourcePeriodicGapDisplacement_apply] using
      normalizedStandardRoot_add_ne_zero (τ x.2) (q x.2) x.1 hτne
  have hd := hτj.sub analyticAt_fst
  have hsum : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => 4*(τ t.2-t.1+w t)) x :=
    analyticAt_const.mul (hd.add hw)
  have hK : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      ((τ t.2-t.1)/(4*(τ t.2-t.1+w t)) + 2*(τ t.2-t.1)*B t.2 + q t.2*(B t.2)^2)/w t) x :=
    (((hd.div hsum (mul_ne_zero (by norm_num) hplus)).add
      ((analyticAt_const.mul hd).mul hBj)).add (hqj.mul (hBj.pow 2))).div hw hwne
  have hE := H.criticalRatioExtension_joint n x ⟨hx.1,fun m _ => hx.2 m⟩
  have hfun : sourceNormalizedActionCircleIntegrandJoint hp hp1 n =
      (fun t : ℂ × CoeffPair p =>
        ((τ t.2-t.1)/(4*(τ t.2-t.1+w t)) + 2*(τ t.2-t.1)*B t.2 + q t.2*(B t.2)^2)/w t *
          sourceCriticalRootRatioExtension hp hp1 n t.2 t.1) := by
    funext t
    simp only [sourceNormalizedActionCircleIntegrandJoint,normalizedActionCircleKernel,
      τ,q,B,w,sourceStandardRoot,sourcePeriodicGapDisplacement_apply]
  rw [hfun]
  exact hK.mul hE

/-- Every fixed-circle candidate is analytic on its full common local neighborhood. -/
theorem SourceActionContourFamily.analytic_normalizedActionCircleCandidate
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceNormalizedActionCircleCandidate hp hp1 n (C.center n : ℂ) (C.radius n)) V := by
  have ha := analyticOnNhd_circleIntegral_of_jointAnalytic
    (sourceNormalizedActionCircleIntegrandJoint hp hp1 n)
    H.criticalOffsets.previous.previous.joint.1 (H.normalizedKernel_joint n)
    (C.center n : ℂ) (C.radius n) ((C.inner_pos n).trans (C.inner_lt n)).le hV
    (fun ψ hψ z hz => ⟨hVW hψ,C.collar_subset_rootDomain hD ψ hψ n (C.sphere_subset_collar n hz)⟩)
  intro ψ hψ
  exact analyticAt_const.mul (ha ψ hψ)

end NLS.ZakharovShabat
