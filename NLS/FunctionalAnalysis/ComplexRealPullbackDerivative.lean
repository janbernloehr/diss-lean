import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Complex.Basic

/-! The derivative of an actual complex-differentiable scalar function
pulled back by a bounded REAL-linear map, on full Banach directions. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem fderiv_complex_real_pullback_apply (f : E → ℂ) (L : D →L[ℝ] E) (u h : D)
    (hf : DifferentiableAt ℂ f (L u)) :
    (fderiv ℝ (fun x => f (L x)) u) h=(fderiv ℂ f (L u)) (L h) := by
  have hd := ((hf.hasFDerivAt.restrictScalars ℝ).comp u L.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f (L x)) u= _ at hd
  rw [hd]
  rfl

end NLS.FunctionalAnalysis
