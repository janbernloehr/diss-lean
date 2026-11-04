import NLS.ZakharovShabat.SourceRealBandGeometry
import NLS.ZakharovShabat.EvenRealCanonicalCriticalPoints
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle

/-! # The indexed bands adjacent to actual canonical contour crossings

Gap membership of critical points identifies the intervening band locally;
actual period-circle separation fixes both crossings without gap openness.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A cut-free real point between consecutive canonical critical points lies in their intervening band. -/
theorem sourceRealBand_of_between_canonicalCriticalPoints (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hr : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : (x : ℂ) ∈ sourceCanonicalRootDomain hp hp1 φ)
    (hl : (canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re < x)
    (hu : x < (canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re) :
    x ∈ sourceRealBand hp hp1 φ n := by
  have hcn := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hr) n
  have hcu := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hr) (n+1)
  constructor
  · by_contra h
    exact hx n (sourcePeriodicSegment_mem_of_realIcc hp hp1 φ hr n x
      ⟨hcn.1.trans hl.le,le_of_not_gt h⟩)
  · by_contra h
    exact hx (n+1) (sourcePeriodicSegment_mem_of_realIcc hp hp1 φ hr (n+1) x
      ⟨le_of_not_gt h,hu.le.trans hcu.2⟩)

/-- Every actual period circle crosses the two bands immediately adjacent to its indexed gap. -/
theorem sourcePeriodCircle_real_crossings_mem_adjacentBands (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hr : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (D : SourceCriticalRootPeriodCircle hp hp1 φ n) :
    D.center-D.radius ∈ sourceRealBand hp hp1 φ (n-1) ∧
      D.center+D.radius ∈ sourceRealBand hp hp1 φ n := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  have hl := re_bounds_of_mem_realCenteredBall (D.gap (left_mem_segment ℝ (l n) (r n)))
  have hu := re_bounds_of_mem_realCenteredBall (D.gap (right_mem_segment ℝ (l n) (r n)))
  have hprev := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hr) (show n-1<n by omega)
  have hnext := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hr) (show n<n+1 by omega)
  have hp := D.other (n-1) (by omega) (r (n-1)) (right_mem_segment ℝ (l (n-1)) (r (n-1)))
  have hn := D.other (n+1) (by omega) (l (n+1)) (left_mem_segment ℝ (l (n+1)) (r (n+1)))
  have hp' : (r (n-1)).re < D.center-D.radius := by
    rcases hp with hp | hp
    · exact hp
    · change (r (n-1)).re < (l n).re at hprev
      linarith [hl.2]
  have hn' : D.center+D.radius < (l (n+1)).re := by
    rcases hn with hn | hn
    · change (r n).re < (l (n+1)).re at hnext
      linarith [hu.1]
    · exact hn
  exact ⟨by simpa only [sourceRealBand,sub_add_cancel] using! And.intro hp' hl.1,
    ⟨hu.2,hn'⟩⟩

end NLS.ZakharovShabat
