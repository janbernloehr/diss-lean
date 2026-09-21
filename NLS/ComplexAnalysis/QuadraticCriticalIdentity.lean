import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Critical-point identities for a quadratic factor

Differentiating a discriminant factorization yields an identity that never
divides by the gap length. Rearrangement isolates the squared-gap factor;
only the final solved formula requires a nonzero coefficient.
-/

open Complex
namespace NLS.ComplexAnalysis

/-- The differentiated quadratic factorization at a critical point. -/
theorem quadratic_factor_critical_identity (D G : ℂ → ℂ) (τ γ c : ℂ)
    (hD : DifferentiableAt ℂ D c) (hG : DifferentiableAt ℂ G c)
    (he : ∀ z, D z^2-4 = -4*((z-τ)^2-γ^2/4)*G z) (hc : deriv D c = 0) :
    2*(c-τ)*G c+((c-τ)^2-γ^2/4)*deriv G c = 0 := by
  have hl := (hD.hasDerivAt.pow 2).sub_const 4
  have hr := (((((hasDerivAt_id c).sub_const τ).pow 2).sub_const (γ^2/4)).mul
    hG.hasDerivAt).const_mul (-4)
  have hf : (fun z => D z^2-4) = fun z => -4*(((z-τ)^2-γ^2/4)*G z) := by
    funext z
    rw [he]
    ring
  change HasDerivAt (fun z => D z^2-4) _ c at hl
  rw [hf] at hl
  have hd := hl.unique hr
  simp only [hc,Pi.pow_apply,id_eq] at hd
  linear_combination hd / 4

/-- The critical offset is multiplied by a coefficient close to twice the remaining product. -/
theorem quadratic_critical_offset_identity (a γ g d : ℂ)
    (h : 2*a*g+(a^2-γ^2/4)*d = 0) :
    (2*g+a*d)*a = γ^2*(d/4) := by
  linear_combination h

/-- Solving the offset identity divides only by the coefficient, never by the gap. -/
theorem quadratic_critical_offset_eq (a γ g d : ℂ)
    (h : 2*a*g+(a^2-γ^2/4)*d = 0) (hne : 2*g+a*d ≠ 0) :
    a = γ^2*(d/(4*(2*g+a*d))) := by
  have he := quadratic_critical_offset_identity a γ g d h
  calc
    a = (γ^2*(d/4))/(2*g+a*d) := (eq_div_iff hne).mpr (by linear_combination he)
    _ = γ^2*(d/(4*(2*g+a*d))) := by rw [div_mul_eq_div_div]; ring

end NLS.ComplexAnalysis
