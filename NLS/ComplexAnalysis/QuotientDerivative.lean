import NLS.ComplexAnalysis.JointSpectralDerivative
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Fréchet derivative of a scalar quotient
-/

noncomputable section
namespace NLS.ComplexAnalysis

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Evaluate the source Fréchet derivative of a scalar quotient in
an arbitrary direction. -/
theorem fderiv_div_apply
    (N Q : A → ℂ) (x : A)
    (hN : DifferentiableAt ℂ N x)
    (hQ : DifferentiableAt ℂ Q x)
    (hQne : Q x ≠ 0) (v : A) :
    (fderiv ℂ (fun y : A => N y / Q y) x) v =
      ((fderiv ℂ N x) v * Q x - N x * (fderiv ℂ Q x) v) / (Q x)^2 := by
  have hinv : (fderiv ℂ (fun y : A => (Q y)⁻¹) x) v =
      -((Q x)⁻¹ * (fderiv ℂ Q x) v * (Q x)⁻¹) := by
    change (fderiv ℂ (Inv.inv ∘ Q) x) v = _
    rw [fderiv_comp x (differentiableAt_inv hQne) hQ,
      fderiv_inv' hQne]
    simp [ContinuousLinearMap.mulLeftRight_apply]
  have hmul := fderiv_fun_mul hN (hQ.inv hQne)
  have hfun : (fun y : A => N y / Q y) =
      (fun y : A => N y * (Q y)⁻¹) := by
    funext y
    exact div_eq_mul_inv (N y) (Q y)
  rw [hfun]
  change (fderiv ℂ (fun y : A => N y * Q⁻¹ y) x) v = _
  rw [hmul]
  simp only [add_apply, smul_apply, smul_eq_mul, Pi.inv_apply]
  have hfunInv : (Q⁻¹) = (fun y : A => (Q y)⁻¹) := by
    funext y
    rfl
  rw [hfunInv]
  rw [hinv]
  field_simp
  ring

end NLS.ComplexAnalysis
