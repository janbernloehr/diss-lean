import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic

/-! Exact spectral differentiation under the quadratic energy map. -/
noncomputable section
namespace NLS.ComplexAnalysis

theorem deriv_comp_quadratic_shift (f : ℂ → ℂ) (z c : ℂ)
    (hf : DifferentiableAt ℂ f (z^2-c)) :
    deriv (fun w => f (w^2-c)) z = deriv f (z^2-c)*(2*z) := by
  have hg : HasDerivAt (fun w : ℂ => w^2-c) (2*z) z := by
    simpa using! ((hasDerivAt_id z).pow 2).sub_const c
  exact (hf.hasDerivAt.comp z hg).deriv

end NLS.ComplexAnalysis
