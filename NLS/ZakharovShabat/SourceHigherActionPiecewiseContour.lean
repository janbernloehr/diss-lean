import NLS.ZakharovShabat.SourceIndexedHigherAction
import NLS.ComplexAnalysis.PiecewiseContourPeriod
import NLS.ComplexAnalysis.SegmentIsolatingCircles

/-! # Original higher actions on arbitrary piecewise C¹ circuits

Every spectral power retains the literal contour normalization and winding
formula, including reversed and repeated circuits in the original cut disk.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal normalized action integral on a finite piecewise C¹ contour. -/
def sourceHigherActionContour (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (Γ : PiecewiseC1Loop) (k : ℕ) : ℂ :=
  ((k+1:ℂ)*(Real.pi:ℂ))⁻¹*Γ.integral (fun z => z^(k+1)*sourceCriticalRootRatioJoint hp hp1 (z,ψ))

/-- The general contour definition agrees exactly with the existing circle convention. -/
theorem sourceHigherActionContour_circle (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (a : ℂ) (r : ℝ) (k : ℕ) :
    sourceHigherActionContour hp hp1 ψ (PiecewiseC1Loop.circle a r) k = sourceHigherActionCircle hp hp1 ψ a r k := by
  simp only [sourceHigherActionContour,PiecewiseC1Loop.integral_circle,sourceHigherActionCircle]

/-- A complete winding formula on the entire original cut disk. -/
theorem SourceCriticalRootPeriodCircle.higherActionContour_eq_mul_winding
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (Γ : PiecewiseC1Loop) (k : ℕ)
    (hΓ : Γ.Inside (ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n)) :
    sourceHigherActionContour hp hp1 ψ Γ k = sourceIndexedHigherAction hp hp1 n k ψ * Γ.windingIntegral
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
  let f : ℂ → ℂ := fun z => z^(k+1)*sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hana : AnalyticOnNhd ℂ f
      (closedBall (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n) := by
    intro z hz
    apply (analyticAt_id.pow (k+1)).mul
    apply sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
    intro m
    by_cases hm : m = n
    · subst m; exact hz.2
    · exact D.closedBall_subset_omittedDomain hz.1 m hm
  have he := Γ.integral_eq_circleIntegral_mul_winding_of_starConvex_cut f (D.center : ℂ)
    _ r D.radius hr hrR _ hclosed hmid ((convex_segment _ _).starConvex hmid) hsegr hana hΓ
  change ((k+1:ℂ)*(Real.pi:ℂ))⁻¹*Γ.integral f = _
  rw [he,← mul_assoc]
  change sourceHigherActionCircle hp hp1 ψ (D.center : ℂ) r k * _ = _
  let E : SourceCriticalRootPeriodCircle hp hp1 ψ n := {
    center := D.center
    radius := r
    radius_pos := hr
    gap := hsegr
    other := by
      intro m hm w hw
      rcases D.other m hm w hw with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  }
  exact congrArg (· * Γ.windingIntegral _) (sourceIndexedHigherAction_eq_circle E k).symm

/-- A winding-one piecewise C¹ circuit gives the original higher action. -/
theorem SourceCriticalRootPeriodCircle.higherActionContour_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (Γ : PiecewiseC1Loop) (k : ℕ)
    (hΓ : Γ.Inside (ball (D.center : ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ n))
    (hw : Γ.windingIntegral (canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1) :
    sourceHigherActionContour hp hp1 ψ Γ k = sourceIndexedHigherAction hp hp1 n k ψ := by
  rw [D.higherActionContour_eq_mul_winding Γ k hΓ,hw,mul_one]

end NLS.ZakharovShabat
