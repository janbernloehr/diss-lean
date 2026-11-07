import NLS.Articles.KdVPseudomeasures.OriginalHillNegativeModels

/-! The actual native map on the physical fractional Hilbert models.
The full real projection is inactive on every physical source. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

local instance negativeMapSourceNormed (r : ℝ) : NormedSpace ℝ (HillRealNegativeSource r) :=
  fourierRealZeroSubmodule_normedSpace (Weight.sobolev (-r))
local instance negativeMapTargetNormed (r : ℝ) : NormedSpace ℝ (HillRealFractionalTarget r) :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev (1/2-r))

def hillNegativeNativeMap (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : HillRealNegativeSource r) : HillRealFractionalTarget r :=
  hillNegativeFreeFourierEquiv r hr q+
    fourierRealZeroFullProjection (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg _)
      (hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r q))

private theorem negative_defect_raw (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : HillRealNegativeSource r) (k : ℤ) :
    (hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r q)).val k =
      (hillHminusNativeComplexMap (hillNegativeSourceInclusion r hr1 q).val.val).val k-
        halfFourierSymbol k*q.val.val.val k := by
  rw [hillFractionalFourierDefect, sub_val,
    hillFractionalNativeRealization_apply r hr hr1 _ (hillNegativeSourceCoefficients_real r hr1 q),
    hillNegativeSourceCoefficients_rough, negativeSobolevHalfFourierEquiv_apply,
    hillNegativeSourceCoefficients_apply]

private theorem negative_projection_inactive (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : HillRealNegativeSource r) :
    (fourierRealZeroFullProjection (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg _)
      (hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r q))).val.val =
        hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r q) := by
  let d := hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r q)
  have h0 : d.val 0 = 0 := by
    rw [negative_defect_raw, hillHminusNativeComplexMap_zero_mode,
      show q.val.val.val 0 = 0 from q.val.property, mul_zero, sub_self]
  have hd : (⟨d,h0⟩ : zeroModeSubmodule (Weight.signedSobolev (1/2-r)) 2) ∈
      fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) 2 := by
    intro k
    change d.val (-k) = (starRingEnd ℂ) (d.val k)
    rw [negative_defect_raw, negative_defect_raw, map_sub, map_mul,
      halfFourierSymbol_conj, halfFourierSymbol_neg, q.property,
      hillHminusNativeComplexMap_real _ (hillNegativeSourceInclusion r hr1 q).property]
  exact congrArg (fun z : HillRealFractionalTarget r => z.val.val)
    (fourierRealZeroFullProjection_inclusion _ _ (⟨⟨d,h0⟩,hd⟩ : HillRealFractionalTarget r))

theorem hillNegativeNativeMap_apply (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : HillRealNegativeSource r) (k : ℤ) :
    (hillNegativeNativeMap r hr hr1 q).val.val.val k =
      (hillRealSignedMap (hillNegativeSourceInclusion r hr1 q)).val.val.val k := by
  change (hillNegativeFreeFourierEquiv r hr q).val.val.val k+
    (fourierRealZeroFullProjection (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg _)
      (hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r q))).val.val.val k = _
  rw [negative_projection_inactive, negative_defect_raw, hillNegativeFreeFourierEquiv_apply,
    hillRealSignedMap_coe, hillMeanZeroComplexMap_coe]
  ring

theorem hillNegativeNativeMap_inclusion (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : HillRealNegativeSource r) :
    hillNegativeTargetInclusion r hr1 (hillNegativeNativeMap r hr hr1 q) =
      hillRealSignedMap (hillNegativeSourceInclusion r hr1 q) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillNegativeTargetInclusion_apply, hillNegativeNativeMap_apply]

theorem analyticAt_hillNegativeNativeMap (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : HillRealNegativeSource r) : AnalyticAt ℝ (hillNegativeNativeMap r hr hr1) q := by
  have hR : AnalyticAt ℝ (hillFractionalFourierDefect r hr hr1)
      (hillNegativeSourceCoefficients r q) :=
    (analyticAt_hillFractionalFourierDefect r hr hr1
      (hillNegativeSourceCoefficients r q) (hillNegativeSourceCoefficients_real r hr1 q)).restrictScalars
  have hA : AnalyticAt ℝ (hillNegativeFreeFourierEquiv r hr) q :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance
      (HillRealNegativeSource r) inferInstance inferInstance
      (HillRealFractionalTarget r) inferInstance inferInstance
      (hillNegativeFreeFourierEquiv r hr).toContinuousLinearMap q
  have hI : AnalyticAt ℝ (hillNegativeSourceCoefficients r) q :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance
      (HillRealNegativeSource r) inferInstance inferInstance
      (WeightedCoeff (Weight.sobolev (-r)) 2) inferInstance inferInstance
      (hillNegativeSourceCoefficients r) q
  have hQ : AnalyticAt ℝ
      (fourierRealZeroFullProjection (p := 2) (Weight.signedSobolev (1/2-r))
        (Weight.signedSobolev_neg _))
      (hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r q)) :=
    ContinuousLinearMap.analyticAt _ _
  have hRI : AnalyticAt ℝ (fun a : HillRealNegativeSource r =>
      hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r a)) q :=
    hR.comp (f := fun a : HillRealNegativeSource r => hillNegativeSourceCoefficients r a) hI
  exact hA.add (hQ.comp (f := fun a : HillRealNegativeSource r =>
    hillFractionalFourierDefect r hr hr1 (hillNegativeSourceCoefficients r a)) hRI)

end NLS.Articles.KdVPseudomeasures
