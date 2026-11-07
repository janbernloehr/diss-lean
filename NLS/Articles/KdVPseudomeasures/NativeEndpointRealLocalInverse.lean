import NLS.Articles.KdVPseudomeasures.NativeEndpointRealSignedMap
import NLS.FunctionalAnalysis.AnalyticEquivalenceInverse

/-! Actual REAL endpoint local inversion with both inverse identities. -/
noncomputable section
open Filter Topology
namespace NLS.Articles.KdVPseudomeasures

theorem fderiv_hillEndpointRealSignedMap_zero_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (h : HillEndpointRealMeanZeroSource r) (k : ℤ) :
    ((fderiv ℝ (hillEndpointRealSignedMap r hr) 0) h).val.val.val k=
      WeightedCoeff.halfFourierSymbol k*h.val.val.val k := by
  rw [fderiv_hillEndpointRealSignedMap_zero]
  exact WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv_apply r hr.1 h k

theorem exists_hillEndpointRealSignedMap_localInverse (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ g : HillEndpointRealSignedTarget r → HillEndpointRealMeanZeroSource r, AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ q in 𝓝 (0 : HillEndpointRealMeanZeroSource r), g (hillEndpointRealSignedMap r hr q)=q) ∧
      (∀ᶠ z in 𝓝 (0 : HillEndpointRealSignedTarget r), hillEndpointRealSignedMap r hr (g z)=z) ∧
      fderiv ℝ g 0=(WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).symm.toContinuousLinearMap := by
  simpa only [hillEndpointRealSignedMap_zero] using
    NLS.FunctionalAnalysis.exists_localInverse_of_equiv_fderiv
      (analyticAt_hillEndpointRealSignedMap r hr 0)
      (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤)
      (fderiv_hillEndpointRealSignedMap_zero r hr)

end NLS.Articles.KdVPseudomeasures
