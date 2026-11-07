import NLS.ZakharovShabat.SourceCanonicalRootReflection
import NLS.ZakharovShabat.SourceOpenGapComplement

/-! Spectral negation preserves the complement of the noncollapsed cuts
whenever the actual ordered periodic endpoints reflect. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}

theorem SourcePeriodicReflection.neg_mem_openGapComplement_iff
    (h : SourcePeriodicReflection hp hp1 ψ) (z : ℂ) :
    -z ∈ sourceOpenGapComplement hp hp1 ψ ↔ z ∈ sourceOpenGapComplement hp hp1 ψ := by
  constructor
  · intro hz n hn hs
    exact hz (-n) (by simpa only [h.gap_neg n] using hn) ((h.neg_mem_segment_iff n z).mpr hs)
  · intro hz n hn hs
    apply hz (-n) (by simpa only [h.gap_neg n] using hn)
    apply (h.neg_mem_segment_iff (-n) z).mp
    simpa only [neg_neg] using hs

end NLS.ZakharovShabat
