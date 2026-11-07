import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic

/-! A quotient of differentiable scalar functions is stationary in
any direction fixing both its numerator and its nonzero denominator. -/
noncomputable section
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_stationary_scalar_quotient
    (F Q : E → ℂ) (a h : E) (hF : DifferentiableAt ℂ F a)
    (hQ : DifferentiableAt ℂ Q a) (hne : Q a ≠ 0)
    (hFzero : (fderiv ℂ F a) h = 0) (hQzero : (fderiv ℂ Q a) h = 0) :
    (fderiv ℂ (fun b => F b/Q b) a) h = 0 := by
  have hi := (hasFDerivAt_inv hne).comp a hQ.hasFDerivAt
  have hd := hF.hasFDerivAt.fun_mul hi
  simp only [Function.comp_def] at hd
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp [ContinuousLinearMap.comp_apply,hFzero,hQzero]

end NLS.ComplexAnalysis
