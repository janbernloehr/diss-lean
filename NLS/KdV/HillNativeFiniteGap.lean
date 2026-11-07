import NLS.KdV.HillNativeRealSignedMap
import NLS.SequenceSpaces.FourierRealZeroTruncation

/-! The actual native coordinate zero set detects the actual closed
periodic gaps. A finite native output therefore comes from an actual
finite-gap source, without an inverse spectral assumption. -/
noncomputable section
open Set Complex
namespace NLS.KdV

/-- Actual finite-gap potentials: all sufficiently high actual periodic gaps close. -/
def hillRealFiniteGapLocus : Set HillRealMeanZeroSource :=
  {q | ∃ N : ℕ, ∀ n : ℕ+, N ≤ (n:ℕ) → hillHminusCanonicalGapSquare n q.val.val=0}

theorem hillRealSignedMap_positive_eq_zero_iff_gapSquare (q : HillRealMeanZeroSource) (n : ℕ+) :
    (hillRealSignedMap q).val.val.val ((n:ℕ):ℤ)=0 ↔ hillHminusCanonicalGapSquare n q.val.val=0 := by
  let z := hillRealSignedMap q
  have hcoords (k : ℤ) : z.val.val.val k=(hillHminusNativeComplexMap q.val.val).val k := by
    rw [hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]
  have hp : z.val.val.val ((n:ℕ):ℤ)*z.val.val.val (-((n:ℕ):ℤ))=hillHminusCanonicalAction n q.val.val := by
    rw [hcoords,hcoords]
    exact hillHminusNativeComplexMap_action_identity q.val.val
      (real_mem_hillHminusActionAngleNativeDomain q.val.val q.property) n
  have hi := hillHminusCanonicalAction_eq_zero_iff_gapSquare_of_real q.val.val q.property n
  constructor
  · intro hz
    apply hi.mp
    rw [← hp,hz,zero_mul]
  · intro hg
    have hprod : z.val.val.val ((n:ℕ):ℤ)*z.val.val.val (-((n:ℕ):ℤ))=0 := hp.trans (hi.mpr hg)
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · have hr := z.property ((n:ℕ):ℤ)
      rw [h] at hr
      exact (map_eq_zero (starRingEnd ℂ)).mp hr.symm

/-- Pulling back a finite output closes every actual gap past the same cutoff. -/
theorem hillRealFiniteGap_of_map_eq_truncate (q : HillRealMeanZeroSource)
    (z : HillRealSignedTarget) (N : ℕ)
    (he : hillRealSignedMap q=WeightedCoeff.fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) N z) :
    q ∈ hillRealFiniteGapLocus := by
  refine ⟨N,fun n hn => ?_⟩
  apply (hillRealSignedMap_positive_eq_zero_iff_gapSquare q n).mp
  rw [he,WeightedCoeff.fourierRealZeroTruncate_apply,Int.natAbs_natCast,if_neg (by omega)]

end NLS.KdV
