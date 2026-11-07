import NLS.Articles.KdVPseudomeasures.NativeEndpointMeanZeroMap
import NLS.FunctionalAnalysis.AnalyticEquivalenceInverse

/-! Actual complex endpoint local inversion at zero, with BOTH inverse
identities and the exact bounded Fourier inverse derivative. -/
noncomputable section
open Filter Topology
namespace NLS.Articles.KdVPseudomeasures

theorem exists_hillEndpointMeanZeroMap_localInverse (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ g : HillEndpointSignedTarget r → HillEndpointMeanZeroSource r, AnalyticAt ℂ g 0 ∧ g 0=0 ∧
      (∀ᶠ q in 𝓝 (0 : HillEndpointMeanZeroSource r), g (hillEndpointMeanZeroMap r hr q)=q) ∧
      (∀ᶠ z in 𝓝 (0 : HillEndpointSignedTarget r), hillEndpointMeanZeroMap r hr (g z)=z) ∧
      fderiv ℂ g 0=(WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm.toContinuousLinearMap := by
  simpa only [hillEndpointMeanZeroMap_zero] using
    NLS.FunctionalAnalysis.exists_localInverse_of_equiv_fderiv
      (analyticAt_hillEndpointMeanZeroMap_real r hr 0 (endpointNativeInclusion_zero_real r hr))
      (WeightedCoeff.meanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤)
      (fderiv_hillEndpointMeanZeroMap_zero r hr)

end NLS.Articles.KdVPseudomeasures
