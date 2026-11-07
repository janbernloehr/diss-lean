import NLS.Articles.KdVPseudomeasures.NativeEndpointBallCompactImage
import NLS.Articles.KdVPseudomeasures.OriginalEndpointRealCoordinates
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeTorusImage

/-! Literal coefficient-preserving inclusions from the full physical real
endpoint source and signed target into the actual native Hilbert spaces.
The exact Fourier equivalences give the target inclusion without changing
its weights, coefficients or physical real form. -/
noncomputable section
open Set NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- The actual bounded physical real endpoint-source inclusion. -/
def endpointPhysicalNativeSourceInclusion (r : ℝ) (hr : AdmissiblePredualOrder r) :
    HillEndpointRealMeanZeroSource r →L[ℝ] HillRealMeanZeroSource :=
  hillRealMeanZeroProjection.comp (((endpointNativeInclusion r hr).restrictScalars ℝ).comp
    (((WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-r)) ⊤).subtypeL.restrictScalars ℝ).comp
      (WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-r)) ⊤).subtypeL))

theorem endpointPhysicalNativeSourceInclusion_inclusion (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) :
    hillRealMeanZeroInclusion (endpointPhysicalNativeSourceInclusion r hr q)=
      endpointNativeInclusion r hr q.val.val := by
  change hillRealMeanZeroInclusion (hillRealMeanZeroProjection (endpointNativeInclusion r hr q.val.val))= _
  apply hillRealMeanZeroProjection_inclusion
  · exact endpointNativeInclusion_real_source r hr q
  · rw [endpointNativeInclusion_apply]
    exact q.val.property

theorem endpointPhysicalNativeSourceInclusion_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) (k : ℤ) :
    (endpointPhysicalNativeSourceInclusion r hr q).val.val.val k=q.val.val.val k := by
  have he := congrArg (fun a : PeriodOneHminusOne => a.val k)
    (endpointPhysicalNativeSourceInclusion_inclusion r hr q)
  exact he.trans (endpointNativeInclusion_apply r hr q.val.val k)

/-- Exact half-Fourier equivalences identify the literal signed-target inclusion. -/
def endpointPhysicalNativeTargetInclusion (r : ℝ) (hr : AdmissiblePredualOrder r) :
    HillEndpointRealSignedTarget r →L[ℝ] HillRealSignedTarget :=
  (WeightedCoeff.realMeanZeroHalfFourierEquiv 2).toContinuousLinearMap.comp
    ((endpointPhysicalNativeSourceInclusion r hr).comp
      (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm.toContinuousLinearMap)

theorem endpointPhysicalNativeTargetInclusion_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (z : HillEndpointRealSignedTarget r) (k : ℤ) :
    (endpointPhysicalNativeTargetInclusion r hr z).val.val.val k=z.val.val.val k := by
  change (WeightedCoeff.realMeanZeroHalfFourierEquiv 2
    (endpointPhysicalNativeSourceInclusion r hr
      ((WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm z))).val.val.val k= _
  rw [WeightedCoeff.realMeanZeroHalfFourierEquiv_apply,endpointPhysicalNativeSourceInclusion_apply,
    WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv_symm_apply,← mul_assoc,
    WeightedCoeff.halfFourierSymbol_mul_inverse,one_mul]

theorem endpointPhysicalNativeTargetInclusion_injective (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (endpointPhysicalNativeTargetInclusion r hr) := by
  intro a b he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have h := congrArg (fun z : HillRealSignedTarget => z.val.val.val k) he
  simpa only [endpointPhysicalNativeTargetInclusion_apply] using h

/-- The actual endpoint map is the literal restriction of the actual native map. -/
theorem endpointPhysicalNativeTargetInclusion_map (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) :
    endpointPhysicalNativeTargetInclusion r hr (hillEndpointRealSignedMap r hr q)=
      hillRealSignedMap (endpointPhysicalNativeSourceInclusion r hr q) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [endpointPhysicalNativeTargetInclusion_apply,hillRealSignedMap_coordinate,
    endpointPhysicalNativeSourceInclusion_inclusion]
  rw [hillEndpointRealSignedMap_coe,hillEndpointMeanZeroMap_real_coordinate r hr _
    (endpointNativeInclusion_real_source r hr q)]
  rfl

/-- The original physical distribution realization commutes with the native inclusion. -/
theorem endpointPhysicalNativeSourceInclusion_original (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) :
    endpointPhysicalNativeSourceInclusion r hr (originalEndpointRealSource r hr q)=
      originalHillRealMeanZeroSource (sourceOriginalPotential r hr q) := by
  apply hillRealMeanZeroInclusion_injective
  rw [endpointPhysicalNativeSourceInclusion_inclusion,originalEndpointRealSource_native,
    originalHillRealMeanZeroSource_inclusion]
  rfl

/-- The actual original endpoint restriction and actual native map have the SAME full output. -/
theorem endpointPhysicalNativeTargetInclusion_originalMap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) :
    endpointPhysicalNativeTargetInclusion r hr (originalEndpointRealSignedCoordinates r hr q)=
      hillRealSignedMap (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)) := by
  change endpointPhysicalNativeTargetInclusion r hr
    (hillEndpointRealSignedMap r hr (originalEndpointRealSource r hr q))= _
  rw [endpointPhysicalNativeTargetInclusion_map,endpointPhysicalNativeSourceInclusion_original]

end NLS.Articles.KdVPseudomeasures
