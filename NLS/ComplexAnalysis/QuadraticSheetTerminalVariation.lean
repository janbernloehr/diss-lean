import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! # A moving quadratic-sheet terminal value

The cleared variation of `delta * H / K` follows from its ordinary
quotient differential, the quadratic-sheet identity and its variation,
and the quadratic differential equation for `H`. Only `K` must be nonzero;
the terminal sheet coordinate may vanish.
-/

noncomputable section
namespace NLS.ComplexAnalysis

theorem quadratic_sheet_terminal_variation
    (δ K Q A H H' g u dδ dK dβ : ℂ) (hK : K ≠ 0)
    (hsq : δ^2 = K^2*Q)
    (hsheet : δ*dδ = K*dK*Q+K^2*A*u)
    (heq : Q*H'+A*H = g)
    (hβ : K^2*dβ = (dδ*K-δ*dK)*H+δ*K*H'*u) :
    δ*dβ = K*g*u := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hK)
  linear_combination δ*hβ+K*H*hsheet-H*dK*hsq+K*H'*u*hsq+K^3*u*heq

/-- When the moving root has velocity `delta * v`, its sheet flow
determines the terminal variation even where `delta` vanishes. -/
theorem quadratic_sheet_terminal_variation_of_flow
    (δ K Q A H H' g v K' dδ dK dβ : ℂ) (hK : K ≠ 0)
    (hsq : δ^2 = K^2*Q)
    (hδ : dδ = (K*K'*Q+K^2*A)*v)
    (hKflow : dK = K'*δ*v)
    (heq : Q*H'+A*H = g)
    (hβ : K^2*dβ = (dδ*K-δ*dK)*H+δ*K*H'*(δ*v)) :
    dβ = K*g*v := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hK)
  linear_combination hβ+K*H*hδ-δ*H*hKflow+
    K*H'*v*hsq-K'*H*v*hsq+K^3*v*heq

end NLS.ComplexAnalysis
