import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! # Exact derivative parity under spectral reflection -/
noncomputable section
namespace NLS.ComplexAnalysis

theorem deriv_neg_argument_of_even (f : ℂ → ℂ) (he : ∀ z, f (-z) = f z) (z : ℂ) :
    deriv f (-z) = -deriv f z := by
  have h := congrArg (fun g : ℂ → ℂ => deriv g z) (funext he)
  rw [deriv_comp_neg] at h
  exact neg_eq_iff_eq_neg.mp h

theorem deriv_zero_of_even (f : ℂ → ℂ) (he : ∀ z, f (-z) = f z) : deriv f 0 = 0 := by
  have h := deriv_neg_argument_of_even f he 0
  simp only [neg_zero] at h
  linear_combination h / 2

theorem second_deriv_neg_argument_of_even (f : ℂ → ℂ) (he : ∀ z, f (-z) = f z) (z : ℂ) :
    deriv (deriv f) (-z) = deriv (deriv f) z := by
  have h := congrArg (fun g : ℂ → ℂ => deriv g z)
    (funext (deriv_neg_argument_of_even f he))
  rw [deriv_comp_neg,deriv.fun_neg] at h
  exact neg_injective h

end NLS.ComplexAnalysis
