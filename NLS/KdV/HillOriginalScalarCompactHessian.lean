import NLS.KdV.HillOriginalCoordinateCompactHessian
import NLS.SequenceSpaces.NatL2CompactScalarHessian

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

/-- Pairing the ACTUAL original spectral sequence with ANY full sequence
has compact Hessian at EVERY original real mean-zero source. The finite
coordinate approximation converges in operator norm on the source dual. -/
theorem isCompactOperator_hillOriginalMeanZeroSpectralPairing_hessian
    (q : hillRealMeanZeroSourceSubmodule) (c : lp (fun _ : ℕ => ℂ) 2) :
    IsCompactOperator (fderiv ℝ (fderiv ℝ
      (fun p => inner ℝ c (hillOriginalMeanZeroRealSpectralMap p))) q) :=
  NLS.SequenceSpaces.isCompactOperator_secondDerivative_natL2_inner _ q
    (analyticOnNhd_hillOriginalMeanZeroRealSpectralMap q (Set.mem_univ _))
    (isCompactOperator_hillOriginalMeanZeroCoordinate_secondDerivative q) c

end NLS.KdV
