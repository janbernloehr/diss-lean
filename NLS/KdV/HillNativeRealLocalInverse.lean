import NLS.KdV.HillNativeRealSignedMap
import NLS.FunctionalAnalysis.AnalyticEquivalenceInverse

/-! The ACTUAL real signed coordinate map is locally analytically
invertible at0 on the physical real mean-zero Banach spaces. -/
noncomputable section
open Filter Topology
namespace NLS.KdV

theorem fderiv_hillRealSignedMap_zero_apply (h : HillRealMeanZeroSource) (k : ℤ) :
    ((fderiv ℝ hillRealSignedMap 0) h).val.val.val k=
      WeightedCoeff.halfFourierSymbol k*h.val.val.val k := by
  rw [fderiv_hillRealSignedMap_zero]
  exact WeightedCoeff.realMeanZeroHalfFourierEquiv_apply h k

theorem exists_hillRealSignedMap_localInverse :
    ∃ g : HillRealSignedTarget → HillRealMeanZeroSource, AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ q in 𝓝 (0 : HillRealMeanZeroSource), g (hillRealSignedMap q)=q) ∧
      (∀ᶠ z in 𝓝 (0 : HillRealSignedTarget), hillRealSignedMap (g z)=z) ∧
      fderiv ℝ g 0=(WeightedCoeff.realMeanZeroHalfFourierEquiv 2).symm.toContinuousLinearMap := by
  simpa only [hillRealSignedMap_zero] using
    NLS.FunctionalAnalysis.exists_localInverse_of_equiv_fderiv
      (analyticAt_hillRealSignedMap 0) (WeightedCoeff.realMeanZeroHalfFourierEquiv 2)
      fderiv_hillRealSignedMap_zero

end NLS.KdV
