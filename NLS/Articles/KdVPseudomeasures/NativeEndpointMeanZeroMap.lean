import NLS.Articles.KdVPseudomeasures.NativeEndpointFirstVariation
import NLS.SequenceSpaces.MeanZeroNegativeOrderHalfFourierEquiv

/-! The ACTUAL endpoint map between the correct closed mean-zero
Banach spaces. The projection retains the whole actual value at real sources. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

abbrev HillEndpointMeanZeroSource (r : ℝ) := WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-r)) ⊤
abbrev HillEndpointSignedTarget (r : ℝ) := WeightedCoeff.zeroModeSubmodule (Weight.signedSobolev (1/2-r)) ⊤

def hillEndpointMeanZeroMap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointMeanZeroSource r) : HillEndpointSignedTarget r :=
  WeightedCoeff.zeroModeProjection (Weight.signedSobolev (1/2-r)) (hillEndpointSignedMap r hr q.val)

theorem hillEndpointMeanZeroMap_real_coe (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointMeanZeroSource r) (hq : IsRealPeriodOneHminusOne (endpointNativeInclusion r hr q.val)) :
    (hillEndpointMeanZeroMap r hr q).val=hillEndpointSignedMap r hr q.val := by
  apply WeightedCoeff.zeroModeProjection_coe
  rw [hillEndpointSignedMap_real_coordinate r hr q.val hq,hillHminusNativeComplexMap_zero_mode]

theorem hillEndpointMeanZeroMap_real_coordinate (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointMeanZeroSource r) (hq : IsRealPeriodOneHminusOne (endpointNativeInclusion r hr q.val)) (k : ℤ) :
    (hillEndpointMeanZeroMap r hr q).val.val k=
      (hillHminusNativeComplexMap (endpointNativeInclusion r hr q.val)).val k := by
  rw [hillEndpointMeanZeroMap_real_coe r hr q hq,hillEndpointSignedMap_real_coordinate r hr q.val hq]

theorem analyticAt_hillEndpointMeanZeroMap_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointMeanZeroSource r) (hq : IsRealPeriodOneHminusOne (endpointNativeInclusion r hr q.val)) :
    AnalyticAt ℂ (hillEndpointMeanZeroMap r hr) q := by
  exact ((WeightedCoeff.zeroModeProjection (Weight.signedSobolev (1/2-r))).analyticAt _).comp
    ((analyticAt_hillEndpointSignedMap_real r hr q.val hq).comp
      ((WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-r)) ⊤).subtypeL.analyticAt q))

theorem hillEndpointMeanZeroMap_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    hillEndpointMeanZeroMap r hr 0=0 := by
  unfold hillEndpointMeanZeroMap
  rw [show ((0 : HillEndpointMeanZeroSource r) : WeightedCoeff (Weight.sobolev (-r)) ⊤)=0 from rfl,
    hillEndpointSignedMap_zero,map_zero]

theorem fderiv_hillEndpointMeanZeroMap_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    fderiv ℂ (hillEndpointMeanZeroMap r hr) 0=
      (WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).toContinuousLinearMap := by
  let S := WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-r)) ⊤
  have hN := (analyticAt_hillEndpointSignedMap_real r hr 0 (endpointNativeInclusion_zero_real r hr)).differentiableAt
  have hi : HasFDerivAt (hillEndpointSignedMap r hr) (fderiv ℂ (hillEndpointSignedMap r hr) 0)
      (S.subtypeL 0) := by simpa only [map_zero] using hN.hasFDerivAt
  have hd := ((WeightedCoeff.zeroModeProjection (Weight.signedSobolev (1/2-r))).hasFDerivAt.comp 0
    (hi.comp 0 S.subtypeL.hasFDerivAt)).fderiv
  change fderiv ℂ (hillEndpointMeanZeroMap r hr) 0=_ at hd
  rw [hd]
  apply ContinuousLinearMap.ext
  intro h
  apply Subtype.ext
  change (WeightedCoeff.zeroModeProjection (Weight.signedSobolev (1/2-r))
    ((fderiv ℂ (hillEndpointSignedMap r hr) 0) h.val) : WeightedCoeff (Weight.signedSobolev (1/2-r)) ⊤)=_
  rw [fderiv_hillEndpointSignedMap_eq_Fourier_on_mean_zero r hr h.val h.property]
  exact WeightedCoeff.zeroModeProjection_coe _ _ (by
    rw [WeightedCoeff.negativeOrderHalfFourierEquiv_apply,show h.val.val 0=0 from h.property,mul_zero])

end NLS.Articles.KdVPseudomeasures
