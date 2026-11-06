import NLS.KdV.HillOriginalDerivativeCompactDefect
import NLS.KdV.HillOriginalDerivativeDenseRange
import NLS.FunctionalAnalysis.ClosedRangeCompactNormal

noncomputable section
set_option autoImplicit false
open Set
namespace NLS.KdV

/-- The ACTUAL original sequence derivative has closed range at EVERY
original real mean-zero source, including every collapsed spectral gap. -/
theorem isClosed_range_fderiv_hillOriginalMeanZeroRealSpectralMap
    (q : hillRealMeanZeroSourceSubmodule) :
    IsClosed (range (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q)) :=
  NLS.FunctionalAnalysis.isClosed_range_of_compact_normal_defect _
    (isCompactOperator_hillOriginalMeanZeroDerivative_normal_defect q)

/-- The ACTUAL original spectral sequence derivative is onto at EVERY
original real mean-zero source. Both dense range and closed range are
proved for the same original derivative, with no inverse hypothesis. -/
theorem surjective_fderiv_hillOriginalMeanZeroRealSpectralMap
    (q : hillRealMeanZeroSourceSubmodule) :
    Function.Surjective (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q) :=
  surjective_fderiv_hillOriginalMeanZeroRealSpectralMap_of_closed_range q
    (isClosed_range_fderiv_hillOriginalMeanZeroRealSpectralMap q)

end NLS.KdV
