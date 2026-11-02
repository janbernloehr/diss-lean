import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! # A uniform local inverse bound for exponentially growing cosh

The free growth is removed before estimating the derivative remainder.
One radius then works at every phase with a common lower bound on its
normalized hyperbolic sine, even at arbitrarily large real part.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_sinh_increment_weighted_le (a w : ℂ) (ha : 0 ≤ a.re) (hw : ‖w‖ ≤ 1) :
    Real.exp (-a.re) * ‖sinh (a+w) - sinh a‖ ≤ 2 * ‖w‖ := by
  let E := Real.exp (-a.re)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hplus : E * ‖exp a‖ = 1 := by
    rw [norm_exp, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hminus : E * ‖exp (-a)‖ ≤ 1 := by
    rw [norm_exp, neg_re, ← Real.exp_add]
    exact (Real.exp_le_exp.mpr (by linarith : -a.re + -a.re ≤ 0)).trans_eq Real.exp_zero
  have h₁ : E * (‖exp a‖ * ‖exp w - 1‖) ≤ 2 * ‖w‖ := by
    rw [← mul_assoc, hplus, one_mul]
    exact norm_exp_sub_one_le hw
  have h₂ : E * (‖exp (-a)‖ * ‖exp (-w) - 1‖) ≤ 2 * ‖w‖ := by
    rw [← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hminus (norm_nonneg _)).trans
      (by simpa only [one_mul, norm_neg] using norm_exp_sub_one_le (x := -w) (by simpa using hw))
  have heq : sinh (a+w) - sinh a =
      (exp a * (exp w - 1) - exp (-a) * (exp (-w) - 1)) / 2 := by
    rw [sinh, sinh, neg_add, exp_add, exp_add]
    ring
  rw [heq, norm_div, norm_ofNat]
  have hh := mul_le_mul_of_nonneg_left
    (norm_sub_le (exp a * (exp w - 1)) (exp (-a) * (exp (-w) - 1))) hE
  simp only [norm_mul, mul_add] at hh
  dsimp only [E] at h₁ h₂ hh
  nlinarith

theorem norm_phase_sub_le_weighted_cosh_error (a u v : ℂ) (c ε : ℝ)
    (ha : 0 ≤ a.re) (hc : 0 < c) (hε : ε ≤ 1) (hsmall : 4*ε ≤ c)
    (hsinh : c ≤ Real.exp (-a.re) * ‖sinh a‖) (hu : ‖u‖ ≤ ε) (hv : ‖v‖ ≤ ε) :
    ‖u-v‖ ≤ Real.exp (-a.re) / c * ‖2*cosh (a+u) - 2*cosh (a+v)‖ := by
  let E := Real.exp (-a.re)
  let R : ℂ → ℂ := fun w => (E : ℂ) * (cosh (a+w) - cosh a - sinh a*w)
  have hd (w : ℂ) : HasDerivAt R ((E : ℂ) * (sinh (a+w) - sinh a)) w := by
    convert! ((((hasDerivAt_id w).const_add a).ccosh.sub_const (cosh a)).sub
      ((hasDerivAt_id w).const_mul (sinh a))).const_mul (E : ℂ) using 1; simp
  have hnorm (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ε) :
      ‖(E : ℂ) * (sinh (a+w) - sinh a)‖ ≤ 2*ε := by
    have hwε : ‖w‖ ≤ ε := by simpa only [mem_closedBall, dist_zero_right] using hw
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact (norm_sinh_increment_weighted_le a w ha (hwε.trans hε)).trans (by linarith)
  have hlip := (convex_closedBall (0 : ℂ) ε : Convex ℝ (closedBall (0 : ℂ) ε)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (hd w).hasDerivWithinAt) hnorm
    (show u ∈ closedBall (0 : ℂ) ε by simpa using hu)
    (show v ∈ closedBall (0 : ℂ) ε by simpa using hv)
  rw [norm_sub_rev (R v), norm_sub_rev v] at hlip
  have hlinear : (E : ℂ) * sinh a * (u-v) =
      (E : ℂ) * (cosh (a+u) - cosh (a+v)) - (R u - R v) := by dsimp [R]; ring
  have ht := norm_sub_le ((E : ℂ) * (cosh (a+u) - cosh (a+v))) (R u - R v)
  rw [← hlinear, norm_mul, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le] at ht
  have hlower := mul_le_mul_of_nonneg_right hsinh (norm_nonneg (u-v))
  have hcerror : c * ‖u-v‖ ≤ E * ‖2*cosh (a+u) - 2*cosh (a+v)‖ := by
    have hnormtrace : ‖2*cosh (a+u) - 2*cosh (a+v)‖ = 2 * ‖cosh (a+u) - cosh (a+v)‖ := by
      rw [← mul_sub, norm_mul, norm_ofNat]
    rw [hnormtrace]
    have hnormE : ‖(E : ℂ) * (cosh (a+u) - cosh (a+v))‖ = E * ‖cosh (a+u) - cosh (a+v)‖ := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    rw [hnormE] at ht
    dsimp only [E] at ht hlower ⊢
    nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg (u-v))]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  calc
    ‖u-v‖ * c = c * ‖u-v‖ := mul_comm _ _
    _ ≤ E * ‖2*cosh (a+u) - 2*cosh (a+v)‖ := hcerror

end NLS.ComplexAnalysis
