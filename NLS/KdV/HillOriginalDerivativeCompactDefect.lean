import NLS.KdV.HillOriginalSourceHilbertStructure
import NLS.KdV.HillOriginalScalarCompactHessian
import NLS.FunctionalAnalysis.NormPreservingCompactDerivativeDefect

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

/-- At EVERY ORIGINAL real mean-zero source, the ACTUAL spectral derivative
has compact normal defect. This uses the exact original norm trace and
actual compact scalar Hessians; no Fourier or Fredholm remainder is assumed. -/
theorem isCompactOperator_hillOriginalMeanZeroDerivative_normal_defect
    (q : hillRealMeanZeroSourceSubmodule) :
    IsCompactOperator (ContinuousLinearMap.id ℝ hillRealMeanZeroSourceSubmodule-
      (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q).adjoint.comp
        (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q)) :=
  NLS.FunctionalAnalysis.isCompactOperator_id_sub_adjoint_comp_fderiv_of_norm_map _
    analyticOnNhd_hillOriginalMeanZeroRealSpectralMap
    norm_hillOriginalMeanZeroRealSpectralMap q
    (isCompactOperator_hillOriginalMeanZeroSpectralPairing_hessian q _)

end NLS.KdV
