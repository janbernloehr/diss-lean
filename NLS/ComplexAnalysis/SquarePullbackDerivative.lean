import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic

/-! Recover the energy derivative from a local square-frequency pullback.
This uses a local equality near a nonzero frequency, without a square-root
branch or an analyticity assumption stronger than differentiability. -/
noncomputable section
open Filter
open scoped Topology
namespace NLS.ComplexAnalysis

theorem deriv_eq_of_square_pullback (f g : ℂ → ℂ) (z d : ℂ) (hz : z ≠ 0)
    (hf : DifferentiableAt ℂ f (z^2)) (hg : HasDerivAt g d z)
    (he : (fun w => f (w^2)) =ᶠ[𝓝 z] g) :
    deriv f (z^2) = d/(2*z) := by
  have hc : HasDerivAt (fun w => f (w^2)) (deriv f (z^2)*(2*z)) z := by
    simpa using! hf.hasDerivAt.comp z ((hasDerivAt_id z).pow 2)
  have hh := (hc.congr_of_eventuallyEq he.symm).unique hg
  exact (eq_div_iff (mul_ne_zero (by norm_num) hz)).2 hh

end NLS.ComplexAnalysis
