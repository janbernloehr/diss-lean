import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Uniform bounds for polynomial remainders with continuous coefficients

A polynomial with spatially continuous coefficients and a zero of order
`N` has a uniform `C*|w|^N` bound on a compact spatial interval and the
closed unit disc in its complex argument.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem continuous_polynomial_function_coeff_mul
    (P Q : Polynomial (ℝ → ℂ)) (hP : ∀ n : ℕ, Continuous (P.coeff n))
    (hQ : ∀ n : ℕ, Continuous (Q.coeff n)) (n : ℕ) : Continuous ((P*Q).coeff n) := by
  rw [Polynomial.coeff_mul]
  have hs := continuous_finsetSum (s := Finset.antidiagonal n)
    (f := fun ij x => P.coeff ij.1 x*Q.coeff ij.2 x)
    (fun ij _ => (hP ij.1).mul (hQ ij.2))
  simpa only [← Pi.mul_apply,← Finset.sum_apply] using! hs

theorem continuous_polynomial_function_eval
    (P : Polynomial (ℝ → ℂ)) (hP : ∀ n : ℕ, Continuous (P.coeff n)) :
    Continuous (fun v : ℝ × ℂ => P.eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) v.1) v.2) := by
  simp only [Polynomial.eval₂_eq_sum,Polynomial.sum]
  apply continuous_finsetSum
  intro n _
  exact ((hP n).comp continuous_fst).mul (continuous_snd.pow n)

/-- Vanishing low coefficients give a uniform power bound, including at
`w = 0`. The constant is independent of both space and inverse frequency. -/
theorem exists_polynomial_function_power_bound
    (Q : Polynomial (ℝ → ℂ)) (hQ : ∀ n : ℕ, Continuous (Q.coeff n))
    (N : ℕ) (hdiv : Polynomial.X^N ∣ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖Q.eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w‖ ≤ C*‖w‖^N := by
  obtain ⟨P,he⟩ := hdiv
  have hP (n : ℕ) : Continuous (P.coeff n) := by
    have hc : Q.coeff (n+N) = P.coeff n := by
      rw [he,Polynomial.coeff_X_pow_mul]
    rw [← hc]
    exact hQ (n+N)
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) 1)).exists_bound_of_continuousOn
    (continuous_polynomial_function_eval P hP).continuousOn
  let C := max M 0+1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right M 0]
  refine ⟨C,hC,?_⟩
  intro x hx w hw
  have hb : ‖P.eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w‖ ≤ C := by
    apply (hM (x,w) ⟨hx,by simpa only [mem_closedBall,dist_zero_right] using hw⟩).trans
    dsimp [C]
    linarith [le_max_left M 0]
  rw [he,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X,norm_mul,norm_pow]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg w) N)).trans_eq (mul_comm _ _)

end NLS.ComplexAnalysis
