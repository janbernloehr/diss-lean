import NLS.SequenceSpaces.HilbertCotangent
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Gradients and Hessians of scalar analytic ℓ² functions

The unconjugated coefficient representation of a complex differential
is an ℓ²-valued analytic gradient. Differentiating this representation
identifies the scalar Hessian with bilinear pairing against its derivative.
-/
noncomputable section
open Set Complex
namespace NLS.Coeff

/-- The complex bilinear gradient of a scalar function on ℓ². -/
def scalarGradient (H : Coeff 2 → ℂ) (b : Coeff 2) : Coeff 2 :=
  hilbertCotangentCoefficients (fderiv ℂ H b)

@[simp] theorem scalarGradient_apply (H : Coeff 2 → ℂ) (b : Coeff 2) (n : ℤ) :
    scalarGradient H b n = fderiv ℂ H b (lp.single 2 n 1) :=
  hilbertCotangentCoefficients_apply _ n

/-- The full differential is recovered on every direction, not only on basis vectors. -/
theorem fderiv_eq_dualPairing_scalarGradient (H : Coeff 2 → ℂ) (b h : Coeff 2) :
    fderiv ℂ H b h = dualPairing (scalarGradient H b) h :=
  (dualPairing_hilbertCotangentCoefficients _ h).symm

/-- The gradient is analytic on the same domain as the scalar function. -/
theorem analyticOnNhd_scalarGradient (H : Coeff 2 → ℂ) {V : Set (Coeff 2)}
    (hH : AnalyticOnNhd ℂ H V) : AnalyticOnNhd ℂ (scalarGradient H) V := by
  intro b hb
  exact (hilbertCotangentCoefficients.analyticAt _).comp (hH.fderiv b hb)

/-- The second scalar derivative pairs the gradient derivative with the second direction. -/
theorem hessian_eq_dualPairing_gradient_derivative (H : Coeff 2 → ℂ) (b : Coeff 2)
    (hH : AnalyticAt ℂ H b) (v w : Coeff 2) :
    fderiv ℂ (fderiv ℂ H) b v w = dualPairing (fderiv ℂ (scalarGradient H) b v) w := by
  have hd := (hilbertCotangentCoefficients.hasFDerivAt.comp b hH.fderiv.differentiableAt.hasFDerivAt).fderiv
  have he : fderiv ℂ (scalarGradient H) b v = hilbertCotangentCoefficients (fderiv ℂ (fderiv ℂ H) b v) := by
    exact congrArg (fun L : Coeff 2 →L[ℂ] Coeff 2 => L v) hd
  rw [he,dualPairing_hilbertCotangentCoefficients]

end NLS.Coeff
