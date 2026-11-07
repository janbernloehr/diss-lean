import NLS.KdV.HillNativeMeanZeroComplexMap
import NLS.ComplexAnalysis.AnalyticEquivDerivativeInverse

/-! A genuine analytic local inverse of the ACTUAL signed complex map
between the correct mean-zero Banach spaces, with its exact Fourier derivative. -/
noncomputable section
open Filter Topology
namespace NLS.KdV

theorem exists_hillMeanZeroComplexMap_localInverse :
    ∃ g : HillSignedComplexTarget → HillMeanZeroSource, AnalyticAt ℂ g 0 ∧ g 0=0 ∧
      (∀ᶠ q in 𝓝 (0 : HillMeanZeroSource), g (hillMeanZeroComplexMap q)=q) ∧
      (∀ᶠ z in 𝓝 (0 : HillSignedComplexTarget), hillMeanZeroComplexMap (g z)=z) ∧
      fderiv ℂ g 0=(WeightedCoeff.meanZeroHalfFourierEquiv 2).symm.toContinuousLinearMap := by
  simpa only [hillMeanZeroComplexMap_zero] using
    NLS.ComplexAnalysis.exists_localInverse_of_equiv_fderiv
      (analyticOnNhd_hillMeanZeroComplexMap 0 zero_mem_hillMeanZeroComplexDomain)
      (WeightedCoeff.meanZeroHalfFourierEquiv 2) fderiv_hillMeanZeroComplexMap_zero

end NLS.KdV
