import NLS.Articles.KdVPseudomeasures.SourceWeightedSpectral

/-! Flat scalar compatibility for the actual diagonal under the original
coefficient-preserving weighted source adapter. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.Fourier
namespace NLS.Articles.KdVPseudomeasures

theorem sourceEndpointDiagonal_forgetWeight (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (n : ℕ)
    (Q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (z : ℂ) :
    (sourceEndpointEntries r hr n (sourceForgetWeight w r Q,z)).1 =
      endpointDiagonal r hr.1 hr.2 n
        (endpointForgetWeight w r (sourceWeightedEndpointCoefficients w r Q),z) := by
  change endpointDiagonal r hr.1 hr.2 n (sourceEndpointCoefficients r (sourceForgetWeight w r Q),z)=_
  exact congrArg (fun a => endpointDiagonal r hr.1 hr.2 n (a,z))
    (sourceEndpointCoefficients_forgetWeight w r Q)

end NLS.Articles.KdVPseudomeasures
