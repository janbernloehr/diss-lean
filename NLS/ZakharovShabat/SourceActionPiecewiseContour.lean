import NLS.ZakharovShabat.SourceIndexedAction
import NLS.ComplexAnalysis.PiecewiseContourPeriod
import NLS.ComplexAnalysis.SegmentIsolatingCircles

/-!
# Equation (2.16) on arbitrary piecewise C¹ circuits

The actual weighted contour integral equals the indexed action times the
winding integral about the selected midpoint. In particular winding-one
circuits give the same action, even in different original isolating disk
families. Neither a chosen homotopy nor a primitive is an input.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal normalized action integral on a finite piecewise C¹ contour. -/
def sourceActionContour (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (Γ : PiecewiseC1Loop) : ℂ :=
  (Real.pi : ℂ)⁻¹*Γ.integral (fun z => z*sourceCriticalRootRatioJoint hp hp1 (z,ψ))

/-- The general contour definition agrees exactly with the existing circle convention. -/
theorem sourceActionContour_circle (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (a : ℂ) (r : ℝ) :
    sourceActionContour hp hp1 ψ (PiecewiseC1Loop.circle a r) = sourceActionCircle hp hp1 ψ a r := by
  simp only [sourceActionContour,PiecewiseC1Loop.integral_circle,sourceActionCircle]

/-- A complete winding formula on the entire original cut disk. -/
theorem SourceCriticalRootPeriodCircle.actionContour_eq_mul_winding
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n)) :
    sourceActionContour hp hp1 ψ Γ = sourceIndexedAction hp hp1 n ψ * Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) := by
  obtain ⟨r,s,hr,hrs,hsR,hsegr⟩ :=
    exists_nested_radii_of_segment_subset_ball _ _ (D.center : ℂ) D.radius D.gap
  have hrR : r < D.radius := hrs.trans hsR
  have hclosed : IsClosed (sourcePeriodicSegment hp hp1 ψ n) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  let f : ℂ → ℂ := fun z => z*sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hana : AnalyticOnNhd ℂ f
      (closedBall (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n) := by
    intro z hz
    apply analyticAt_id.mul
    apply sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
    intro m
    by_cases hm : m = n
    · subst m; exact hz.2
    · exact D.closedBall_subset_omittedDomain hz.1 m hm
  have he := Γ.integral_eq_circleIntegral_mul_winding_of_starConvex_cut f (D.center : ℂ)
    _ r D.radius hr hrR _ hclosed hmid ((convex_segment _ _).starConvex hmid) hsegr hana hΓ
  change (Real.pi : ℂ)⁻¹*Γ.integral f = _
  rw [he,← mul_assoc]
  change sourceActionCircle hp hp1 ψ (D.center : ℂ) r * _ = _
  rw [sourceActionCircle_eq_of_nested_enclosingCircles hp hp1 ψ n
    (D.center : ℂ) (D.center : ℂ) r D.radius hr D.radius_pos hsegr D.gap
    (closedBall_subset_closedBall hrR.le) D.closedBall_subset_omittedDomain,
    sourceIndexedAction_eq_circle D]

/-- All piecewise C¹ contours in the original disk have the indexed
winding formula, including repeated and reversed traversals. -/
theorem SourceIsolatingNeighborhoods.actionContour_eq_mul_winding
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n)) :
    sourceActionContour hp hp1 ψ Γ = sourceIndexedAction hp hp1 n ψ * Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) := by
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  exact (hD.periodCircle ψ hψ n a r hr he).actionContour_eq_mul_winding Γ (by
    change Γ.Inside (ball (a : ℂ) r \ sourcePeriodicSegment hp hp1 ψ n)
    rwa [← he])

/-- Every admissible counterclockwise circuit computes equation (2.16). -/
theorem SourceIsolatingNeighborhoods.indexedAction_eq_circuit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n))
    (hwind : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1) :
    sourceIndexedAction hp hp1 n ψ = sourceActionContour hp hp1 ψ Γ := by
  rw [hD.actionContour_eq_mul_winding ψ hψ n Γ hΓ,hwind,mul_one]

/-- The normalized action is independent of both the circuit and the
particular original isolating family. Neither pair of disks needs to be nested. -/
theorem sourceActionContour_eq_of_original_circuits
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V₀ V₁ : Set (CoeffPair p)}
    {D₀ D₁ : ℤ → Set ℂ} {c₀ c₁ : ℝ}
    (hD₀ : SourceIsolatingNeighborhoods hp hp1 V₀ D₀ c₀)
    (hD₁ : SourceIsolatingNeighborhoods hp hp1 V₁ D₁ c₁)
    (ψ : CoeffPair p) (hψ₀ : ψ ∈ V₀) (hψ₁ : ψ ∈ V₁) (n : ℤ)
    (Γ₀ Γ₁ : PiecewiseC1Loop)
    (hΓ₀ : Γ₀.Inside (D₀ n \ sourcePeriodicSegment hp hp1 ψ n))
    (hΓ₁ : Γ₁.Inside (D₁ n \ sourcePeriodicSegment hp hp1 ψ n))
    (hw₀ : Γ₀.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1)
    (hw₁ : Γ₁.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1) :
    sourceActionContour hp hp1 ψ Γ₀ = sourceActionContour hp hp1 ψ Γ₁ :=
  (hD₀.indexedAction_eq_circuit ψ hψ₀ n Γ₀ hΓ₀ hw₀).symm.trans
    (hD₁.indexedAction_eq_circuit ψ hψ₁ n Γ₁ hΓ₁ hw₁)

end NLS.ZakharovShabat
