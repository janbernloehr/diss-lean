import NLS.ZakharovShabat.SourceAbelianDiscJointChart

/-! # Interior charts agree with each other and the exterior

For distinct selected gaps, each chart excludes the other chart's cut.
The shared spectral point therefore stays off all cuts along the source
projection path. Continuous logarithm uniqueness fixes the additive
constant, as it does on overlaps with the old and projected charts.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianDiscJointChart
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Any two normalized interior charts agree, including charts for
 different gaps and charts centered at different real sources. -/
theorem eqOn_overlap (D E : SourceAbelianDiscJointChart hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : EqOn (D.toFun n) (E.toFun n) (D.domain ∩ E.domain) := by
  intro t ht
  by_cases hgap : D.gap = E.gap
  · rcases D with ⟨j,C,φ,r,hr,hsub,hnorm⟩
    rcases E with ⟨k,B,χ,r',hr',hsub',hnorm'⟩
    dsimp only at hgap
    subst k
    exact C.primitive_eqOn_overlap B t.2 (hsub ht.1.1.2).1 (hsub' ht.2.1.2).1 n
      ⟨⟨ht.1.1.1,ht.2.1.1⟩,ht.1.2.2 j⟩
  let L : ℝ → ℂ × CoeffPair p := fun s => (t.1,sourceRealProjectionPath hp t.2 s)
  have hL : Continuous L := by dsimp [L,sourceRealProjectionPath]; fun_prop
  have hpath (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : L s ∈ D.domain ∩ E.domain := by
    have hd := D.projectionPath_mem_ball t.2 ht.1.1.2 s hs
    have he := E.projectionPath_mem_ball t.2 ht.2.1.2 s hs
    have hr : t.1 ∈ sourceCanonicalRootDomain hp hp1 (sourceRealProjectionPath hp t.2 s) := by
      intro k
      by_cases hk : k = D.gap
      · subst k
        exact E.cauchy.avoids_other _ (E.source_subset he).1 (ball_subset_closedBall ht.2.1.1) D.gap hgap
      · exact D.cauchy.avoids_other _ (D.source_subset hd).1 (ball_subset_closedBall ht.1.1.1) k hk
    exact ⟨⟨⟨ht.1.1.1,hd⟩,(D.source_subset hd).2,hr⟩,⟨⟨ht.2.1.1,he⟩,(E.source_subset he).2,hr⟩⟩
  have heq := continuousLogarithms_eqOn (fun s => D.toFun n (L s)) (fun s => E.toFun n (L s))
    (Icc (0:ℝ) 1) isPreconnected_Icc
    ((D.analytic n).continuousOn.comp hL.continuousOn (fun s hs => (hpath s hs).1))
    ((E.analytic n).continuousOn.comp hL.continuousOn (fun s hs => (hpath s hs).2))
    (fun s hs => (D.exp_toFun hD hroot n (L s) (hpath s hs).1).trans (E.exp_toFun hD hroot n (L s) (hpath s hs).2).symm)
    0 (by simp) (by
      have h0 := hpath 0 (by simp)
      simp only [L,sourceRealProjectionPath_zero] at h0 ⊢
      exact (D.real_eq n (sourceRealTypeProjection hp t.2) t.1 h0.1).trans
        (E.real_eq n (sourceRealTypeProjection hp t.2) t.1 h0.2).symm)
  simpa only [L,sourceRealProjectionPath_one] using heq (show (1:ℝ) ∈ Icc 0 1 by simp)

/-- Interior charts preserve every overlapping old product-chart value. -/
theorem eq_jointChart (D : SourceAbelianDiscJointChart hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (E : SourceAbelianJointChart hp hp1) (n : ℤ) (t : ℂ × CoeffPair p)
    (ht : t ∈ D.domain) (he : t ∈ E.domain) : D.toFun n t = E.toFun n t := by
  let L : ℝ → ℂ × CoeffPair p := fun s => (t.1,sourceRealProjectionPath hp t.2 s)
  have hL : Continuous L := by dsimp [L,sourceRealProjectionPath]; fun_prop
  have hE (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : L s ∈ E.domain := by
    have h := sourceSegmentMap_mem (ball E.center E.radius) (ball E.source.val E.radius)
      (sourceRealTypeProjection hp t.2).val (convex_ball _ _) (E.real_projection_mem t he).2 t he s hs
    simpa only [SourceAbelianJointChart.domain,sourceSegmentMap,Complex.coe_smul,L,sourceRealProjectionPath] using! h
  have hC (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : L s ∈ D.domain := by
    have hb := D.projectionPath_mem_ball t.2 ht.1.2 s hs
    exact ⟨⟨ht.1.1,hb⟩,(D.source_subset hb).2,E.root_domain (L s) (hE s hs)⟩
  have heq := continuousLogarithms_eqOn (fun s => D.toFun n (L s)) (fun s => E.toFun n (L s))
    (Icc (0:ℝ) 1) isPreconnected_Icc
    ((D.analytic n).continuousOn.comp hL.continuousOn hC)
    ((E.analytic n).continuousOn.comp hL.continuousOn hE)
    (fun s hs => (D.exp_toFun hD hroot n (L s) (hC s hs)).trans
      (sourceAbelianLogChart_exp hp hp1 E.source.val E.source.property E.center n (L s)
        (E.root_domain (E.center,E.source.val) E.center_mem) (E.root_domain (L s) (hE s hs))).symm)
    0 (by simp) (by
      have h0 := hC 0 (by simp)
      simp only [L,sourceRealProjectionPath_zero] at h0 ⊢
      exact (D.real_eq n (sourceRealTypeProjection hp t.2) t.1 h0).trans
        (E.real_eq n (sourceRealTypeProjection hp t.2) (E.real_projection_mem t he).2 t.1 he.1).symm)
  simpa only [L,sourceRealProjectionPath_one] using heq (show (1:ℝ) ∈ Icc 0 1 by simp)

theorem eq_joint (D : SourceAbelianDiscJointChart hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : EqOn (D.toFun n) (sourceAbelianJointPrimitive hp hp1 n) (D.domain ∩ sourceAbelianJointDomain hp hp1) := by
  intro t ht
  obtain ⟨E,he⟩ := mem_iUnion.mp ht.2
  exact (D.eq_jointChart hD hroot E n t ht.1 he).trans (sourceAbelianJointPrimitive_eq_chart hp hp1 n E he).symm

/-- The projection path also identifies the interior and projected
 functions on their entire overlap, beyond the original collar. -/
theorem eq_projected (D : SourceAbelianDiscJointChart hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : EqOn (D.toFun n) (sourceAbelianProjectedPrimitive hp hp1 n)
      (D.domain ∩ sourceAbelianProjectedDomain hp hp1 W) := by
  intro t ht
  have hM := sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot
  let L : ℝ → ℂ × CoeffPair p := fun s => (t.1,sourceRealProjectionPath hp t.2 s)
  have hL : Continuous L := by dsimp [L,sourceRealProjectionPath]; fun_prop
  have hP (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : L s ∈ sourceAbelianProjectedDomain hp hp1 W :=
    sourceRealProjectionPath_mem_projectedDomain hp hp1 W t.1 t.2 ht.2 s hs
  have hC (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : L s ∈ D.domain :=
    ⟨⟨ht.1.1.1,D.projectionPath_mem_ball t.2 ht.1.1.2 s hs⟩,sourceAbelianProjectedDomain_end hp hp1 W (hP s hs)⟩
  have hPc : ContinuousOn (sourceAbelianProjectedPrimitive hp hp1 n) (sourceAbelianProjectedDomain hp hp1 W) :=
    fun u hu => (continuousAt_sourceAbelianProjectedPrimitive hp hp1 W hD hM n u hu).continuousWithinAt
  have heq := continuousLogarithms_eqOn (fun s => D.toFun n (L s)) (fun s => sourceAbelianProjectedPrimitive hp hp1 n (L s))
    (Icc (0:ℝ) 1) isPreconnected_Icc
    ((D.analytic n).continuousOn.comp hL.continuousOn hC) (hPc.comp hL.continuousOn hP)
    (fun s hs => (D.exp_toFun hD hroot n (L s) (hC s hs)).trans
      (sourceAbelianProjectedPrimitive_exp hp hp1 W hM n (L s) (hP s hs)).symm)
    0 (by simp) (by
      have h0 := hC 0 (by simp)
      simp only [L,sourceRealProjectionPath_zero,sourceAbelianProjectedPrimitive_eq_real] at h0 ⊢
      exact D.real_eq n (sourceRealTypeProjection hp t.2) t.1 h0)
  simpa only [L,sourceRealProjectionPath_one] using heq (show (1:ℝ) ∈ Icc 0 1 by simp)

/-- Every old exterior value is retained by an overlapping disc chart. -/
theorem eq_enlarged (D : SourceAbelianDiscJointChart hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : EqOn (D.toFun n) (sourceAbelianEnlargedPrimitive hp hp1 W n)
      (D.domain ∩ sourceAbelianEnlargedDomain hp hp1 W) := by
  intro t ht
  rcases ht.2 with hold | hproj
  · exact (D.eq_joint hD hroot n ⟨ht.1,hold⟩).trans
      (sourceAbelianEnlargedPrimitive_eq_joint hp hp1 W hD (sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot) n hold).symm
  · exact (D.eq_projected hD hroot n ⟨ht.1,hproj⟩).trans
      (sourceAbelianEnlargedPrimitive_eq_projected hp hp1 W n hproj).symm

end NLS.ZakharovShabat.SourceAbelianDiscJointChart
