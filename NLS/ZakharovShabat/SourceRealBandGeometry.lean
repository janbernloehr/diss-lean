import NLS.ZakharovShabat.SourceStandardRootOmittedParitySign
import NLS.ZakharovShabat.SourceCriticalRootRatioOuterArcs

/-! # Geometry of the real spectral band between consecutive gaps -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The open real band between gap `n` and gap `n+1`. -/
def sourceRealBand (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : Set ℝ :=
  Ioo (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re

/-- The band remains nonempty even if either neighboring gap is collapsed. -/
theorem sourceRealBand_nonempty (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (sourceRealBand hp hp1 φ n).Nonempty :=
  nonempty_Ioo.mpr (canonicalPeriodicRight_re_lt_next_left hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n)

/-- From the right endpoint of gap `n` up to the next gap, every other
standard root stays on a real exterior ray. -/
theorem sourceRealBand_exterior_other_gaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ico
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re)
    (m : ℤ) (hm : m ≠ n) :
    x < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m).re ∨
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m).re < x := by
  have horder (k : ℤ) := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 k)
  rcases lt_or_gt_of_ne hm with hmn | hnm
  · right
    exact (canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) hmn).trans_le
      ((horder n).trans hx.1)
  · left
    by_cases he : m = n+1
    · simpa only [he] using hx.2
    · have hnm' : n+1 < m := by omega
      exact hx.2.trans_le ((horder (n+1)).trans
        (canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) hnm').le)

/-- The left-closed band avoids every cut except possibly its selected
left gap at the shared endpoint. -/
theorem sourceRealBand_leftClosed_subset_omittedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ico
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re) :
    (x : ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 φ n := by
  intro m hm hmem
  have hI := sourcePeriodicSegment_re_mem_Icc hp hp1 φ m (x : ℂ) hmem
  rcases sourceRealBand_exterior_other_gaps hp hp1 φ hφ n x hx m hm with h | h
  · exact h.not_ge hI.1
  · exact h.not_ge hI.2

/-- Every point strictly inside the band is off every canonical cut. -/
theorem sourceRealBand_subset_rootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ sourceRealBand hp hp1 φ n) : (x : ℂ) ∈ sourceCanonicalRootDomain hp hp1 φ := by
  intro m
  by_cases hm : m = n
  · subst m
    intro hmem
    exact hx.1.not_ge (sourcePeriodicSegment_re_mem_Icc hp hp1 φ n (x : ℂ) hmem).2
  · exact sourceRealBand_leftClosed_subset_omittedDomain hp hp1 φ hφ n x ⟨hx.1.le,hx.2⟩ m hm

end NLS.ZakharovShabat
