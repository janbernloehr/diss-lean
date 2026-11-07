import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalLocalHomeomorph
import NLS.KdV.HillNativeFiniteGap
import NLS.KdV.HillClosedGapRigidity
import NLS.FunctionalAnalysis.ClosedLocalHomeomorph

/-! The ACTUAL native physical real map has exactly one zero-fiber point.
Borg rigidity is proved on the full original real Hminus-one domain by
actual Miura/Dirac data; no global native injectivity is assumed. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- ACTUAL vanishing native coordinates force the original physical source to vanish. -/
theorem hillRealSignedMap_eq_zero_iff (q : HillRealMeanZeroSource) :
    hillRealSignedMap q=0 ↔ q=0 := by
  constructor
  · intro h
    have hg (n : ℕ+) : hillHminusCanonicalGapSquare n (hillRealMeanZeroInclusion q)=0 := by
      apply (hillRealSignedMap_positive_eq_zero_iff_gapSquare q n).mp
      rw [h]
      rfl
    have hq := hillHminus_eq_zero_of_mean_zero_all_gapSquares_zero (hillRealMeanZeroInclusion q)
      q.property q.val.property hg
    apply hillRealMeanZeroInclusion_injective
    simpa only [map_zero] using hq
  · rintro rfl
    exact hillRealSignedMap_zero

/-- The EXACT zero fiber of the ACTUAL native physical real map. -/
theorem hillRealSignedMap_zero_fiber : hillRealSignedMap ⁻¹' ({0} : Set HillRealSignedTarget)={0} := by
  ext q
  exact hillRealSignedMap_eq_zero_iff q

/-- Borg zero-mean rigidity in the ENTIRE original physical distribution domain. -/
theorem original_Hill_eq_zero_of_all_gapSquares_zero (q : OriginalHminusOnePotential)
    (hgap : ∀ n : ℕ+, hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q)=0) :
    q.val=0 := by
  have hz := hillHminus_eq_zero_of_mean_zero_all_gapSquares_zero (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) (originalPeriodOneCoefficients_mean_zero q) hgap
  calc
    q.val=periodOneOriginal (originalPeriodOneCoefficients q) :=
      (periodOneOriginal_originalPeriodOneCoefficients q).symm
    _=0 := by rw [hz,map_zero]

/-- ACTUAL native zero-output uniqueness retains the SAME entire original potential. -/
theorem original_Hill_native_zero_implies_zero (q : OriginalHminusOnePotential)
    (hz : hillRealSignedMap (originalHillRealMeanZeroSource q)=0) : q.val=0 := by
  have hq := (hillRealSignedMap_eq_zero_iff _).mp hz
  have hc := congrArg hillRealMeanZeroInclusion hq
  rw [originalHillRealMeanZeroSource_inclusion,map_zero] at hc
  calc
    q.val=periodOneOriginal (originalPeriodOneCoefficients q) :=
      (periodOneOriginal_originalPeriodOneCoefficients q).symm
    _=0 := by rw [hc,map_zero]

/-- The remaining ACTUAL global bijectivity problem is EXACTLY closedness
of the SAME native map. The closed-map condition is NOT asserted proved. -/
theorem hillPhysicalNative_bijective_iff_isClosedMap :
    Function.Bijective hillRealSignedMap ↔ IsClosedMap hillRealSignedMap := by
  constructor
  · intro h
    exact ((Equiv.ofBijective hillRealSignedMap h).toHomeomorphOfContinuousOpen
      (continuous_iff_continuousAt.mpr (fun q => (analyticAt_hillRealSignedMap q).continuousAt))
      hillPhysicalNativeMap_isOpenMap).isClosedMap
  · intro hc
    exact NLS.FunctionalAnalysis.bijective_of_closed_localHomeomorph_singleton_fiber
      hillRealSignedMap hillPhysicalNativeMap_isLocalHomeomorph hc 0
      (fun q hq => (hillRealSignedMap_eq_zero_iff q).mp
        (by simpa only [hillRealSignedMap_zero] using hq))

end NLS.Articles.KdVPseudomeasures
