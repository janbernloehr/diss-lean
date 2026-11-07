import NLS.Articles.KdVPseudomeasures.NativeEndpointMeanZeroMap
import NLS.SequenceSpaces.RealNegativeOrderHalfFourierEquiv

/-! The ACTUAL endpoint restriction on the physical real mean-zero
Banach source, with its true real signed target and exact Fourier derivative. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

abbrev HillEndpointRealMeanZeroSource (r : ℝ) := WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-r)) ⊤
abbrev HillEndpointRealSignedTarget (r : ℝ) := WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) ⊤

theorem endpointNativeInclusion_real_source (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) :
    IsRealPeriodOneHminusOne (endpointNativeInclusion r hr q.val.val) := by
  intro k
  rw [endpointNativeInclusion_apply,endpointNativeInclusion_apply]
  exact q.property k

theorem hillEndpointMeanZeroMap_mem_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) :
    hillEndpointMeanZeroMap r hr q.val ∈ WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) ⊤ := by
  intro k
  rw [hillEndpointMeanZeroMap_real_coordinate r hr q.val (endpointNativeInclusion_real_source r hr q),
    hillEndpointMeanZeroMap_real_coordinate r hr q.val (endpointNativeInclusion_real_source r hr q)]
  exact hillHminusNativeComplexMap_real _ (endpointNativeInclusion_real_source r hr q) k

def hillEndpointRealSignedMap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) : HillEndpointRealSignedTarget r :=
  WeightedCoeff.fourierRealZeroProjection (p := ⊤) (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg (1/2-r))
    (hillEndpointMeanZeroMap r hr q.val)

theorem hillEndpointRealSignedMap_coe (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) :
    (hillEndpointRealSignedMap r hr q).val=hillEndpointMeanZeroMap r hr q.val :=
  WeightedCoeff.fourierRealZeroProjection_coe _ _ _ (hillEndpointMeanZeroMap_mem_real r hr q)

theorem analyticAt_hillEndpointRealSignedMap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) : AnalyticAt ℝ (hillEndpointRealSignedMap r hr) q := by
  have hP : AnalyticAt ℝ
      (WeightedCoeff.fourierRealZeroProjection (p := ⊤) (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg (1/2-r)))
      (hillEndpointMeanZeroMap r hr q.val) := _root_.ContinuousLinearMap.analyticAt _ _
  have hI : AnalyticAt ℝ
      ((WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-r)) ⊤).subtypeL :
        HillEndpointRealMeanZeroSource r →L[ℝ] HillEndpointMeanZeroSource r) q := _root_.ContinuousLinearMap.analyticAt _ _
  have hN : AnalyticAt ℝ (fun a : HillEndpointRealMeanZeroSource r => hillEndpointMeanZeroMap r hr a.val) q :=
    (analyticAt_hillEndpointMeanZeroMap_real r hr q.val (endpointNativeInclusion_real_source r hr q)).restrictScalars.comp
      (f := fun a : HillEndpointRealMeanZeroSource r => a.val) hI
  exact hP.comp (f := fun a : HillEndpointRealMeanZeroSource r => hillEndpointMeanZeroMap r hr a.val) hN

theorem analyticOnNhd_hillEndpointRealSignedMap (r : ℝ) (hr : AdmissiblePredualOrder r) :
    AnalyticOnNhd ℝ (hillEndpointRealSignedMap r hr) univ :=
  fun q _ => analyticAt_hillEndpointRealSignedMap r hr q

theorem hillEndpointRealSignedMap_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    hillEndpointRealSignedMap r hr 0=0 := by
  unfold hillEndpointRealSignedMap
  rw [show ((0 : HillEndpointRealMeanZeroSource r) : HillEndpointMeanZeroSource r)=0 from rfl,
    hillEndpointMeanZeroMap_zero,map_zero]

theorem fderiv_hillEndpointRealSignedMap_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    fderiv ℝ (hillEndpointRealSignedMap r hr) 0=
      (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).toContinuousLinearMap := by
  let S := WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-r)) ⊤
  have hC := (analyticAt_hillEndpointMeanZeroMap_real r hr 0 (endpointNativeInclusion_zero_real r hr)).differentiableAt.hasFDerivAt
  rw [fderiv_hillEndpointMeanZeroMap_zero] at hC
  have hi : HasFDerivAt (hillEndpointMeanZeroMap r hr)
      ((WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).toContinuousLinearMap.restrictScalars ℝ)
      (S.subtypeL 0) := by simpa only [map_zero] using hC.restrictScalars ℝ
  have hI : HasFDerivAt (S.subtypeL : HillEndpointRealMeanZeroSource r →L[ℝ] HillEndpointMeanZeroSource r) S.subtypeL 0 :=
    _root_.ContinuousLinearMap.hasFDerivAt _
  have hP : HasFDerivAt
      (WeightedCoeff.fourierRealZeroProjection (p := ⊤) (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg (1/2-r)))
      (WeightedCoeff.fourierRealZeroProjection (p := ⊤) (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg (1/2-r)))
      (hillEndpointMeanZeroMap r hr (S.subtypeL 0)) := _root_.ContinuousLinearMap.hasFDerivAt _
  have hN : HasFDerivAt (fun q : HillEndpointRealMeanZeroSource r => hillEndpointMeanZeroMap r hr q.val)
      (((WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).toContinuousLinearMap.restrictScalars ℝ).comp S.subtypeL) 0 :=
    hi.comp (𝕜 := ℝ) (E := HillEndpointRealMeanZeroSource r) (F := HillEndpointMeanZeroSource r) (G := HillEndpointSignedTarget r)
      (f := fun q : HillEndpointRealMeanZeroSource r => q.val) 0 hI
  have hFinal : HasFDerivAt (hillEndpointRealSignedMap r hr)
      ((WeightedCoeff.fourierRealZeroProjection (p := ⊤) (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg (1/2-r))).comp
        (((WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).toContinuousLinearMap.restrictScalars ℝ).comp S.subtypeL)) 0 := by
    exact @HasFDerivAt.comp ℝ inferInstance
      (HillEndpointRealMeanZeroSource r) inferInstance inferInstance
      (HillEndpointSignedTarget r) inferInstance inferInstance
      (HillEndpointRealSignedTarget r) inferInstance inferInstance
      (fun q : HillEndpointRealMeanZeroSource r => hillEndpointMeanZeroMap r hr q.val)
      (((WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).toContinuousLinearMap.restrictScalars ℝ).comp S.subtypeL) 0
      _ _ hP hN
  rw [hFinal.fderiv]
  apply ContinuousLinearMap.ext
  intro h
  apply Subtype.ext
  change (WeightedCoeff.fourierRealZeroProjection (p := ⊤) (Weight.signedSobolev (1/2-r))
    (Weight.signedSobolev_neg (1/2-r)) (WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤ h.val) :
      HillEndpointSignedTarget r)=_
  exact WeightedCoeff.fourierRealZeroProjection_coe _ _ _
    (WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv_real r hr.1 h.val h.property)

end NLS.Articles.KdVPseudomeasures
