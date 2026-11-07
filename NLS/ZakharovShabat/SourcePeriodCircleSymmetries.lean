import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ZakharovShabat.SourceGapSymmetries

/-! # Transport of the actual isolating circles

Spectral negation preserves the orientation of a circuit. These are
original circles at the transformed source, with all other gaps still
strictly separated; no symmetric choice of circles is assumed.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceCriticalRootPeriodCircle
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p} {n : ℤ}

def spectralNegation (D : SourceCriticalRootPeriodCircle hp hp1 φ n) (χ : CoeffPair p)
    (h : ∀ m z, -z ∈ sourcePeriodicSegment hp hp1 χ (-m) ↔
      z ∈ sourcePeriodicSegment hp hp1 φ m) : SourceCriticalRootPeriodCircle hp hp1 χ (-n) where
  center := -D.center
  radius := D.radius
  radius_pos := D.radius_pos
  gap := by
    intro w hw
    have hw' : -w ∈ sourcePeriodicSegment hp hp1 φ n := (h n (-w)).mp (by simpa using hw)
    have hb := D.gap hw'
    rw [mem_ball,ofReal_neg,← dist_neg_neg w (- (D.center : ℂ)),neg_neg]
    exact hb
  other := by
    intro m hm w hw
    have hmn : -m ≠ n := by intro he; apply hm; omega
    have hw' : -w ∈ sourcePeriodicSegment hp hp1 φ (-m) :=
      (h (-m) (-w)).mp (by simpa using hw)
    rcases D.other (-m) hmn (-w) hw' with hl | hr
    · right; simp only [neg_re] at hl; linarith
    · left; simp only [neg_re] at hr; linarith

def componentSwap (D : SourceCriticalRootPeriodCircle hp hp1 φ n) :
    SourceCriticalRootPeriodCircle hp hp1 (sourceComponentSwap φ) (-n) :=
  D.spectralNegation _ (sourcePeriodicSegment_componentSwap hp hp1 φ)

def midpointReflection (D : SourceCriticalRootPeriodCircle hp hp1 φ n) :
    SourceCriticalRootPeriodCircle hp hp1 (sourceMidpointReflection φ) (-n) :=
  D.spectralNegation _ (sourcePeriodicSegment_midpointReflection hp hp1 φ)

def reciprocalScaling (D : SourceCriticalRootPeriodCircle hp hp1 φ n) (c : ℂ) (hc : c ≠ 0) :
    SourceCriticalRootPeriodCircle hp hp1 (sourceReciprocalScaling c φ) n where
  center := D.center
  radius := D.radius
  radius_pos := D.radius_pos
  gap := by rw [sourcePeriodicSegment_reciprocalScaling hp hp1 c hc]; exact D.gap
  other := by
    intro m hm w hw
    rw [sourcePeriodicSegment_reciprocalScaling hp hp1 c hc] at hw
    exact D.other m hm w hw

end SourceCriticalRootPeriodCircle
end NLS.ZakharovShabat
