import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ZakharovShabat.SourceCanonicalRootReflection

/-! # Reflecting actual isolating circles under spectral negation -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)] {hp : p≠⊤} {hp1 : 1<p}
    {ψ : CoeffPair p} {n : ℤ}

/-- Spectral negation preserves the radius and positive orientation of
an actual isolating circle, and reverses its integer gap label. -/
def SourceCriticalRootPeriodCircle.reflect
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) (h : SourcePeriodicReflection hp hp1 ψ) :
    SourceCriticalRootPeriodCircle hp hp1 ψ (-n) where
  center := -D.center
  radius := D.radius
  radius_pos := D.radius_pos
  gap := by
    intro z hz
    have hw : -z∈sourcePeriodicSegment hp hp1 ψ n := by
      simpa only [neg_neg] using (h.neg_mem_segment_iff (-n) z).mpr hz
    have hb := D.gap hw
    rw [mem_ball,dist_eq_norm] at hb ⊢
    rw [ofReal_neg,show z-(-(D.center:ℂ)) = -((-z)-(D.center:ℂ)) by ring,norm_neg]
    exact hb
  other := by
    intro m hm z hz
    have hmn : -m≠n := by omega
    have hw : -z∈sourcePeriodicSegment hp hp1 ψ (-m) := (h.neg_mem_segment_iff m z).mpr hz
    have hs := D.other (-m) hmn (-z) hw
    simp only [neg_re] at hs
    rcases hs with hs | hs
    · right
      linarith
    · left
      linarith

end NLS.ZakharovShabat
