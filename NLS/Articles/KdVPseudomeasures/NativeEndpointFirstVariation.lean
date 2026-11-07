import NLS.Articles.KdVPseudomeasures.NativeEndpointAnalyticCoordinates
import NLS.KdV.HillNativeMeanZeroComplexMap
import NLS.SequenceSpaces.WeightedCoordinateDerivativeTransfer
import NLS.SequenceSpaces.NegativeOrderHalfFourierEquiv

/-! The FULL endpoint Banach derivative of the ACTUAL nonlinear map,
with exactly the native Fourier symbol on every mean-zero direction. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem endpointNativeInclusion_zero_real (r : ℝ) (hr : AdmissiblePredualOrder r) :
    IsRealPeriodOneHminusOne (endpointNativeInclusion r hr 0) := by
  rw [map_zero]
  intro k
  simp

theorem hillEndpointSignedMap_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    hillEndpointSignedMap r hr 0=0 := by
  apply Subtype.ext
  funext k
  rw [hillEndpointSignedMap_real_coordinate r hr 0 (endpointNativeInclusion_zero_real r hr),
    map_zero,hillHminusNativeComplexMap_zero]
  rfl

theorem fderiv_hillEndpointSignedMap_coordinates (r : ℝ) (hr : AdmissiblePredualOrder r)
    (h : WeightedCoeff (Weight.sobolev (-r)) ⊤) (k : ℤ) :
    ((fderiv ℂ (hillEndpointSignedMap r hr) 0) h).val k=
      ((fderiv ℂ hillHminusNativeComplexMap 0) (endpointNativeInclusion r hr h)).val k := by
  have hreal := endpointNativeInclusion_zero_real r hr
  obtain ⟨U,hU,h0U,_,_,B,_,hbound⟩ := exists_hillEndpointSignedMap_analytic_neighborhood r hr 0 hreal
  have he : ∀ᶠ q in 𝓝 (0 : WeightedCoeff (Weight.sobolev (-r)) ⊤), ∀ j : ℤ,
      (hillEndpointSignedMap r hr q).val j=
        (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val j := by
    filter_upwards [hU.mem_nhds h0U] with q hq
    exact (hbound q hq).2
  have hnative : DifferentiableAt ℂ hillHminusNativeComplexMap 0 :=
    (analyticOnNhd_hillHminusNativeComplexMap 0 (by
      rw [map_zero] at hreal
      exact real_mem_hillHminusActionAngleNativeDomain 0 hreal)).differentiableAt
  exact WeightedCoeff.fderiv_coordinates_comp_linear _ _ (hillEndpointSignedMap r hr)
    hillHminusNativeComplexMap (endpointNativeInclusion r hr)
    (analyticAt_hillEndpointSignedMap_real r hr 0 (endpointNativeInclusion_zero_real r hr)).differentiableAt
    hnative he h k

theorem fderiv_hillEndpointSignedMap_eq_Fourier_on_mean_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (h : WeightedCoeff (Weight.sobolev (-r)) ⊤) (hh : h.val 0=0) :
    (fderiv ℂ (hillEndpointSignedMap r hr) 0) h=WeightedCoeff.negativeOrderHalfFourierEquiv r hr.1 ⊤ h := by
  have hnative : (endpointNativeInclusion r hr h).val 0=0 := by
    rw [endpointNativeInclusion_apply,hh]
  apply Subtype.ext
  funext k
  rw [fderiv_hillEndpointSignedMap_coordinates,
    fderiv_hillHminusNativeComplexMap_eq_halfFourier _ hnative,WeightedCoeff.halfFourierEquiv_apply,
    endpointNativeInclusion_apply,WeightedCoeff.negativeOrderHalfFourierEquiv_apply]

end NLS.Articles.KdVPseudomeasures
