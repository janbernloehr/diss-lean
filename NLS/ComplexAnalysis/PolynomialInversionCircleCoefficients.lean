import NLS.ComplexAnalysis.InversionCircleCoefficients
import NLS.ComplexAnalysis.CirclePolynomialIntegrationByParts
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Every exterior polynomial moment extracts a Taylor coefficient

Repeated closed-contour integration by parts reduces the polynomial weight.
No termwise integration of an infinite Laurent series is required.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- Weight `z^k` extracts the coefficient of order `k+1` of the inversion germ. -/
theorem circleIntegral_pow_mul_comp_inv_eq
    (g : ℂ → ℂ) (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hRr : R⁻¹ < r)
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) (k : ℕ) :
    (∮ z in C(0,R), z^k*g z⁻¹) =
      (2*Real.pi*I : ℂ) * (iteratedDeriv (k+1) g 0 / (k+1).factorial) := by
  induction k generalizing g with
  | zero =>
    simpa only [Nat.zero_add,pow_zero,one_mul,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,div_one] using
      circleIntegral_comp_inv_eq g r R hr hR hRr hg
  | succ k ih =>
    let U : Set ℂ := {z | z ≠ 0 ∧ z⁻¹ ∈ ball (0 : ℂ) r}
    let F : ℂ → ℂ := fun z => g z⁻¹
    have hF : AnalyticOnNhd ℂ F U := fun z hz =>
      (hg z⁻¹ hz.2).comp (analyticAt_id.inv hz.1)
    have hc : sphere (0 : ℂ) R ⊆ U := by
      intro z hz
      have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
      exact ⟨norm_pos_iff.mp (hn.symm ▸ hR),by simpa only [mem_ball,dist_zero_right,norm_inv,hn] using hRr⟩
    have hi := circleIntegral_pow_mul_deriv_eq_neg F U hF 0 R hR.le hc (k+1)
    have he : (∮ z in C(0,R), z^(k+1+1)*deriv F z) =
        -(∮ z in C(0,R), z^k*deriv g z⁻¹) := by
      rw [← neg_one_mul (∮ z in C(0,R), z^k*deriv g z⁻¹),← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hz0 := (hc hz).1
      have hd := ((hg z⁻¹ (hc hz).2).differentiableAt.hasDerivAt.comp z (hasDerivAt_inv hz0)).deriv
      change deriv F z = deriv g z⁻¹ * -(z^2)⁻¹ at hd
      dsimp only
      rw [hd,pow_succ,pow_succ]
      field_simp
    rw [he,ih (deriv g) hg.deriv,← iteratedDeriv_succ'] at hi
    have hn : (k+1+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k+1)
    dsimp only [F] at hi
    have hm : (∮ z in C(0,R), z^(k+1)*g z⁻¹) * (k+1+1 : ℂ) =
        (2*Real.pi*I : ℂ) * (iteratedDeriv (k+1+1) g 0 / (k+1).factorial) := by
      simp only [Nat.cast_add,Nat.cast_one] at hi
      linear_combination hi
    calc
      _ = ((2*Real.pi*I : ℂ) * (iteratedDeriv (k+1+1) g 0 / (k+1).factorial)) / (k+1+1) :=
        (eq_div_iff hn).mpr hm
      _ = _ := by
        simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_inv_rev]
        ring

end NLS.ComplexAnalysis
