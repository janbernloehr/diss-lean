import NLS.ZakharovShabat.SourceSecondMomentFrequencyAnalytic
import NLS.ZakharovShabat.SourceActionSequenceExponent
import NLS.ZakharovShabat.DeletedPeriodicFree

/-! # Spectral actions and renormalized frequencies at the zero source -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every actual spectral action vanishes at the zero source. -/
theorem sourceComplexAction_eq_zero_at_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceComplexAction hp hp1 n 0 = 0 := by
  have hreal : IsRealType (CoeffPair.toMax p 0) := by simp
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n 0 hreal]
  apply (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 0 hreal n).2.2.mpr
  simpa only [sourcePeriodicGapDisplacement_apply,map_zero] using
    canonicalPeriodicGap_zero hp hp1 n

namespace SourceBirkhoffMapComplexData
variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The full action sequence sends the zero source to the zero action. -/
theorem actionSequence_zero (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    sourceActionSequence (q := q) hp hp1 s 0 = 0 := by
  ext n
  exact (D.actionSequence_apply 0 (D.real_subset (0 : realTypeSourceSubmodule p).property) n).trans
    (sourceComplexAction_eq_zero_at_zero hp hp1 n)

end SourceBirkhoffMapComplexData
namespace SourceAbelianMomentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The moment-sum frequency vanishes at zero at every finite source
exponent above one, independently of the chosen normalized atlas. -/
theorem renormalizedFrequency_eq_zero_at_zero (A : SourceAbelianMomentAtlas hp hp1 W s) (n : ℤ) :
    A.renormalizedFrequency n 0 = 0 := by
  have hgap (k : ℤ) : canonicalPeriodicGap hp hp1
      (periodOnePotential (0 : CoeffPair p)) (periodOnePotential_mem 0) k = 0 := by
    simpa only [map_zero] using canonicalPeriodicGap_zero hp hp1 k
  have hmom (k : ℤ) : A.moment n k 2 0 = 0 :=
    A.moment_succ_of_collapsed 0 (A.realType_subset_domain (0 : realTypeSourceSubmodule p).property)
      n k (hgap k) 1
  simp only [renormalizedFrequency,hmom,tsum_zero,mul_zero]

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
