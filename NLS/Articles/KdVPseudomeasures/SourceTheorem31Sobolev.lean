import NLS.Articles.KdVPseudomeasures.OriginalHillNegativeEquivalence
import NLS.Articles.KdVPseudomeasures.OriginalHillNonnegativeSobolevEquiv
import NLS.FunctionalAnalysis.AnalyticEquivTransport
import NLS.SequenceSpaces.SignedRealEqualOrderEquiv

/-! The full all-real-order assertion of Theorem 3.1(ii), including
the rough endpoint and both directions of every fractional analytic map. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

local instance theorem31SourceNormed (s : ℝ) :
    NormedSpace ℝ (fourierRealZeroSubmodule (Weight.sobolev s) 2) :=
  fourierRealZeroSubmodule_normedSpace _
local instance theorem31SignedNormed (s : ℝ) : NormedSpace ℝ (RealSignedHilbert s) :=
  fourierRealZeroSubmodule_normedSpace _

/-- The SAME actual canonical map, with a coefficient-preserving
rough source inclusion, a bijection, and analytic maps in both directions. -/
def SourceHilbertNativeEquivalenceAt (s : ℝ) : Prop :=
  ∃ I : fourierRealZeroSubmodule (Weight.sobolev s) 2 →L[ℝ] HillRealMeanZeroSource,
    (∀ q k, (I q).val.val.val k = q.val.val.val k) ∧
    ∃ e : fourierRealZeroSubmodule (Weight.sobolev s) 2 ≃ RealSignedHilbert (s+1/2),
      (∀ q k, (e q).val.val.val k = (hillRealSignedMap (I q)).val.val.val k) ∧
      (∀ q, AnalyticAt ℝ e q) ∧ (∀ z, AnalyticAt ℝ e.symm z)

theorem sourceHilbertNativeEquivalenceAt_nonnegative (s : ℝ) (hs : 0 ≤ s) :
    SourceHilbertNativeEquivalenceAt s := by
  obtain ⟨e,he,ha,hi⟩ := exists_hillNonnegativeSobolevEquiv s hs
  let A := (physicalSignedSobolevPositiveEquiv s hs 2).symm
  let B := ContinuousLinearEquiv.refl ℝ (RealSignedHilbert (s+1/2))
  let I := (hillNonnegativeSobolevSourceInclusion s hs).comp A.toContinuousLinearMap
  let e' := @linearTransportEquiv ℝ (fourierRealZeroSubmodule (Weight.sobolev s) 2) (RealSignedHilbert s) (RealSignedHilbert (s+1/2)) (RealSignedHilbert (s+1/2))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B
  refine ⟨I,?_,e',?_,?_,?_⟩
  · intro q k
    change (hillNonnegativeSobolevSourceInclusion s hs (A q)).val.val.val k = _
    rw [hillNonnegativeSobolevSourceInclusion_apply, physicalSignedSobolevPositiveEquiv_symm_apply]
  · intro q k
    exact he (A q) k
  · exact @analyticAt_linearTransportEquiv ℝ (fourierRealZeroSubmodule (Weight.sobolev s) 2) (RealSignedHilbert s) (RealSignedHilbert (s+1/2)) (RealSignedHilbert (s+1/2))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B ha
  · exact @analyticAt_linearTransportEquiv_symm ℝ (fourierRealZeroSubmodule (Weight.sobolev s) 2) (RealSignedHilbert s) (RealSignedHilbert (s+1/2)) (RealSignedHilbert (s+1/2))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B hi

theorem sourceHilbertNativeEquivalenceAt_negative (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    SourceHilbertNativeEquivalenceAt (-r) := by
  obtain ⟨e,he,ha,hi⟩ := exists_hillNegativeNativeEquiv r hr hr1
  let A := ContinuousLinearEquiv.refl ℝ (HillRealNegativeSource r)
  let B := signedRealEqualOrderEquiv (1/2-r) (-r+1/2) (by ring)
  refine ⟨hillNegativeSourceInclusion r hr1,hillNegativeSourceInclusion_apply r hr1,
    (@linearTransportEquiv ℝ (HillRealNegativeSource r) (HillRealNegativeSource r) (HillRealFractionalTarget r) (RealSignedHilbert (-r+1/2))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B),?_,?_,?_⟩
  · intro q k
    change (B (e q)).val.val.val k = _
    rw [signedRealEqualOrderEquiv_apply]
    exact he q k
  · exact @analyticAt_linearTransportEquiv ℝ (HillRealNegativeSource r) (HillRealNegativeSource r) (HillRealFractionalTarget r) (RealSignedHilbert (-r+1/2))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B ha
  · exact @analyticAt_linearTransportEquiv_symm ℝ (HillRealNegativeSource r) (HillRealNegativeSource r) (HillRealFractionalTarget r) (RealSignedHilbert (-r+1/2))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B hi

theorem sourceHilbertNativeEquivalenceAt_minus_one : SourceHilbertNativeEquivalenceAt (-1) := by
  let A := ContinuousLinearEquiv.refl ℝ HillRealMeanZeroSource
  let B := signedRealEqualOrderEquiv (-1/2) ((-1:ℝ)+1/2) (by norm_num)
  let e := hillNativeHomeomorph.toEquiv
  refine ⟨ContinuousLinearMap.id ℝ HillRealMeanZeroSource,fun _ _ => rfl,
    (@linearTransportEquiv ℝ HillRealMeanZeroSource HillRealMeanZeroSource HillRealSignedTarget (RealSignedHilbert ((-1:ℝ)+1/2))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B),?_,?_,?_⟩
  · intro q k
    change (B (e q)).val.val.val k = _
    rw [signedRealEqualOrderEquiv_apply]
    rfl
  · exact @analyticAt_linearTransportEquiv ℝ HillRealMeanZeroSource HillRealMeanZeroSource HillRealSignedTarget (RealSignedHilbert ((-1:ℝ)+1/2))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B analyticAt_hillRealSignedMap
  · exact @analyticAt_linearTransportEquiv_symm ℝ HillRealMeanZeroSource HillRealMeanZeroSource HillRealSignedTarget (RealSignedHilbert ((-1:ℝ)+1/2))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance A e B analyticAt_hillNativeHomeomorph_symm

/-- Every real Sobolev order s≥-1, with the correct signed target
order s+1/2, has the actual canonical bianalytic diffeomorphism. -/
theorem sourceTheorem3_1_ii (s : ℝ) (hs : -1 ≤ s) : SourceHilbertNativeEquivalenceAt s := by
  by_cases hpos : 0 ≤ s
  · exact sourceHilbertNativeEquivalenceAt_nonnegative s hpos
  by_cases hmin : s = -1
  · subst s
    exact sourceHilbertNativeEquivalenceAt_minus_one
  have hr : 0 ≤ -s := by linarith
  have hr1 : -s < 1 := by
    have hstrict : -1 < s := lt_of_le_of_ne hs (Ne.symm hmin)
    linarith
  simpa only [neg_neg] using sourceHilbertNativeEquivalenceAt_negative (-s) hr hr1

end NLS.Articles.KdVPseudomeasures
