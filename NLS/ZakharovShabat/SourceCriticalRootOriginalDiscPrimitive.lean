import NLS.ZakharovShabat.SourceCriticalRootPeriodZero
import NLS.ComplexAnalysis.PrimitiveOnDiscComplement
import NLS.ComplexAnalysis.SegmentIsolatingCircles
import NLS.ComplexAnalysis.PiecewiseC1Loop

/-!
# Primitives and closed contours on the original cut disks

Zero periods yield primitives on the whole original disk minus its
selected gap, for every complex source in the retained W. Consequently
every finite piecewise C¹ closed contour there has zero integral, without
requiring a prescribed homotopy, winding number, or real-source condition.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Keep the entire original radius when constructing the primitive. -/
theorem SourceLemma10_11CircleData.exists_cutDisc_primitive
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceCriticalRootRatioJoint hp hp1 (z,ψ)) z := by
  obtain ⟨r,s,hr,hrs,hsR,hsegr⟩ :=
    exists_nested_radii_of_segment_subset_ball _ _ (D.center : ℂ) D.radius D.gap
  have hrR : r < D.radius := hrs.trans hsR
  have hzero : (∮ z in C((D.center : ℂ),r), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
    change (∮ z in C((D.center : ℂ),r),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z) = 0
    rw [circleIntegral_sourceCriticalRootRatio_eq_of_nested_enclosingCircles
      hp hp1 ψ n (D.center : ℂ) (D.center : ℂ) r D.radius hr D.radius_pos hsegr D.gap
      (closedBall_subset_closedBall hrR.le) D.closedBall_subset_omittedDomain]
    exact h.zero ψ hψ n D
  have hclosed : IsClosed (sourcePeriodicSegment hp hp1 ψ n) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  have hana : AnalyticOnNhd ℂ (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ))
      (closedBall (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n) := by
    apply (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).mono
    intro z hz m
    by_cases hm : m = n
    · subst m; exact hz.2
    · exact D.closedBall_subset_omittedDomain hz.1 m hm
  exact exists_primitive_on_disc_complement_of_zero_period _ (D.center : ℂ)
    (sourceStandardRootMidpoint hp hp1 ψ n) r D.radius hr hrR _ hclosed hmid
    ((convex_segment _ _).starConvex hmid) hsegr hana hzero

/-- A primitive on the full original D_n minus its gap, with no real-source
or open-gap restriction. -/
theorem SourceLemma10_11CircleData.originalDisk_primitive
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ) :
    ∃ F : ℂ → ℂ, ∀ z ∈ D n \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceCriticalRootRatioJoint hp hp1 (z,ψ)) z := by
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  rw [he]
  exact h.exists_cutDisc_primitive ψ hψW n (hD.periodCircle ψ hψV n a r hr he)

/-- All piecewise C¹ closed contours in the original cut disk have zero
integral. Corners, repeated traversals and self-intersections are allowed. -/
theorem SourceLemma10_11CircleData.originalDisk_loopIntegral_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n)) :
    Γ.integral (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
  obtain ⟨F,hF⟩ := h.originalDisk_primitive hD ψ hψW hψV n
  have hf : ContinuousOn (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ))
      (D n \ sourcePeriodicSegment hp hp1 ψ n) := by
    apply (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).continuousOn.mono
    intro z hz m
    by_cases hm : m = n
    · subst m; exact hz.2
    · exact hD.disk_subset_omittedDomain ψ hψV n hz.1 m hm
  exact Γ.integral_eq_zero_of_primitive _ F _ hf hF hΓ

end NLS.ZakharovShabat
