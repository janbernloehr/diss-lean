import NLS.KdV.HillHminusFreeLabels
import NLS.KdV.HillActionAngleNativeNorm

/-! All ORIGINAL positive free gaps collapse at their exact labels.
The ACTUAL actions, scalar Cartesian coordinates and full native
Cartesian sequence map therefore vanish at the zero potential. -/
noncomputable section
open Set Complex NLS.LpSequence
open scoped Classical
namespace NLS.KdV

theorem hillHminusCanonicalGapSquare_zero (n : ℕ+) :
    hillHminusCanonicalGapSquare n 0 = 0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hp := hillHminusLabels_free_pair hr n
  rw [hillHminusCanonicalGapSquare_eq_real 0 hr n,hp.1,hp.2,sub_self,zero_pow (by decide : (2:ℕ) ≠ 0)]

theorem hillHminusCanonicalAction_zero (n : ℕ+) : hillHminusCanonicalAction n 0 = 0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  exact (hillHminusCanonicalAction_eq_zero_iff_gapSquare_of_real 0 hr n).mpr
    (hillHminusCanonicalGapSquare_zero n)

theorem hillHminusActionAngle_zero (n : ℕ+) :
    hillHminusActionAngleX n 0 = 0 ∧ hillHminusActionAngleY n 0 = 0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  exact hillHminusActionAngle_zero_of_real_closed_gap n 0 hr (hillHminusCanonicalGapSquare_zero n)

theorem hillHminusNativeCartesianMap_zero : hillHminusNativeCartesianMap 0 = 0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hq := real_mem_hillHminusActionAngleNativeDomain 0 hr
  apply (WeightedCoeffPair.toMax (Weight.positiveSobolev (-1/2)) 2).injective
  apply Prod.ext
  · apply Subtype.ext
    funext k
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨n,rfl⟩ := hk
      change (hillHminusNativeCartesianMap 0).fst.val ((n:ℕ):ℤ) = 0
      rw [(hillHminusNativeCartesianMap_positive 0 hq n).1,(hillHminusActionAngle_zero n).1]
    · change (hillHminusActionAngleXSequence 0).val k = 0
      rw [(hillHminusActionAngle_sequences_coordinates 0 hq k).1,
        positiveScalarExtension_zero_of_not_mem_range _ k hk]
  · apply Subtype.ext
    funext k
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨n,rfl⟩ := hk
      change (hillHminusNativeCartesianMap 0).snd.val ((n:ℕ):ℤ) = 0
      rw [(hillHminusNativeCartesianMap_positive 0 hq n).2,(hillHminusActionAngle_zero n).2]
    · change (hillHminusActionAngleYSequence 0).val k = 0
      rw [(hillHminusActionAngle_sequences_coordinates 0 hq k).2,
        positiveScalarExtension_zero_of_not_mem_range _ k hk]

end NLS.KdV
