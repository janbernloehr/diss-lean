import NLS.DifferentialPolynomial.RiccatiResolventParity
import NLS.ZakharovShabat.NLSRiccatiPolynomials

/-! # The canonical resolvent uses the existing physical Riccati coefficients

This adapter fixes the seed and recurrence by equality with the already used
NLS differential polynomials. Identification of the two resolvent components
with their Euler gradients remains a distinct variational step.
-/
noncomputable section
open NLS.DifferentialPolynomial MvPolynomial
namespace NLS.ZakharovShabat

theorem nlsRiccatiPolynomial_eq_differentialRiccatiSequence :
    nlsRiccatiPolynomial = differentialRiccatiSequence spatialDerivative (X (false,0)) (X (true,0)) :=
  differentialRiccatiSequence_unique spatialDerivative _ _ nlsRiccatiPolynomial
    (nlsRiccatiPolynomial_zero)
    (by simp [nextJet]) nlsRiccatiPolynomial_recurrence

/-- The canonical formal resolvent's Riccati input has exactly the existing
physical hierarchy coefficients, at every order. -/
theorem coeff_nls_differentialRiccatiSeries (n : ℕ) :
    PowerSeries.coeff n
      (differentialRiccatiSeries spatialDerivative (X (false,0)) (X (true,0))) =
        nlsRiccatiPolynomial n := by
  rw [coeff_differentialRiccatiSeries, nlsRiccatiPolynomial_eq_differentialRiccatiSequence]

end NLS.ZakharovShabat
