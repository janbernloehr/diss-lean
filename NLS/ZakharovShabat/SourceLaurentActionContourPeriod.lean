import NLS.ZakharovShabat.SourceLaurentActionContour

/-! # Integer-level action periods on arbitrary close piecewise circuits

The original ground-normalized primitive is analytic on the isolating
disc minus its selected gap. The actual weighted contour integral equals
the circle value times winding, for every integer level when zero is
excluded. Corners, repeated traversals and collapsed gaps are included.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem laurentActionContour_eq_mul_winding
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (r : ℝ) (hinner : C.discs.inner n ≤ r) (houter : r < C.discs.outer n)
    (hzero : (0 : ℂ) ∉ closedBall (C.discs.center n) (C.discs.outer n))
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (C.discs.center n) (C.discs.outer n) \ sourcePeriodicSegment hp hp1 φ.val n)) :
    sourceLaurentActionContour hp hp1 φ k Γ =
      sourceLaurentPrimitiveCircle hp hp1 W n k φ.val (C.discs.center n) r *
        Γ.windingIntegral (canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ.val)
          (periodOnePotential_mem _) n) := by
  have hr : 0 < r := (C.discs.inner_pos n).trans_le hinner
  have hclosed : IsClosed (sourcePeriodicSegment hp hp1 φ.val n) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 φ.val n
  let f : ℂ → ℂ := fun z => z^(k-1)*sourceAbelianPrimitive hp hp1 φ.val φ.property z
  have hana : AnalyticOnNhd ℂ f
      (closedBall (C.discs.center n) (C.discs.outer n) \ sourcePeriodicSegment hp hp1 φ.val n) := by
    intro z hz
    have hn : z ≠ 0 := by intro he; exact hzero (he ▸ hz.1)
    have hroot : z ∈ sourceCanonicalRootDomain hp hp1 φ.val := by
      intro m
      by_cases hm : m = n
      · subst m; exact hz.2
      · exact C.discs.avoids_other φ.val hφ n hz.1 m hm
    exact (analyticAt_id.zpow hn).mul (sourceAbelianPrimitive_analyticAt_of_mem_rootDomain hp hp1
      φ.val φ.property z hroot)
  have hseg := (C.discs.segment_subset φ.val hφ n).trans (ball_subset_ball hinner)
  have he := Γ.integral_eq_circleIntegral_mul_winding_of_starConvex_cut f (C.discs.center n)
    _ r (C.discs.outer n) hr houter _ hclosed hmid ((convex_segment _ _).starConvex hmid) hseg hana hΓ
  obtain ⟨E⟩ := C.charts φ.val hφ
  have hlocal := sourceLaurentActionContour_circle_eq_local hp hp1 W n k φ E (C.discs.center n) r
    hr.le (C.intermediate_circle_root n φ.val hφ r hinner houter)
    (fun hz => hzero (closedBall_subset_closedBall houter.le hz))
  change -(Real.pi : ℂ)⁻¹*Γ.integral f = _
  rw [he,← hlocal,sourceLaurentActionContour,PiecewiseC1Loop.integral_circle]
  simp only [f,mul_assoc]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
