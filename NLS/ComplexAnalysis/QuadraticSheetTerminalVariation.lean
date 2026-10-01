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

/-- The differentiated cosine and terminal sine equations determine
an angle velocity even at either endpoint. -/
theorem quadratic_cosine_angle_variation_of_flow
    (d K K' σ κ e v S dS dK : ℂ) (hd : d ≠ 0) (hK : K ≠ 0)
    (htrig : σ^2+κ^2 = 1)
    (hS : S = -Complex.I*d*K*σ)
    (hroot : -d*σ*e = S*v)
    (hflow : dS = (K*K'*(-d^2*σ^2)+K^2*d*κ)*v)
    (hKflow : dK = K'*S*v)
    (hSderiv : dS = -Complex.I*d*(dK*σ+K*κ*e)) :
    e = Complex.I*K*v := by
  have hsin : σ*(e-Complex.I*K*v) = 0 := by
    apply mul_left_cancel₀ hd
    rw [mul_zero]
    linear_combination -hroot-v*hS
  have hcos : κ*(e-Complex.I*K*v) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hd hK)
    rw [mul_zero]
    linear_combination -Complex.I*hSderiv+Complex.I*hflow-d*σ*hKflow-d*σ*K'*v*hS+
      d*(σ*dK+K*κ*e)*Complex.I_sq
  have he : e-Complex.I*K*v = 0 := by
    linear_combination σ*hsin+κ*hcos-(e-Complex.I*K*v)*htrig
  exact sub_eq_zero.mp he

end NLS.ComplexAnalysis
