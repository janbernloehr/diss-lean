import NLS.ZakharovShabat.FreeSquaredSineBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The literal sine estimates used in Section 8. The exterior quotient
bound has constant four, and the filled sinc retains its cosine integral
at the removable center. These are positive estimates for the source proof. -/
noncomputable section
set_option autoImplicit false
open Set Complex Metric
namespace NLS.ZakharovShabat

/-- The complex sine norm retains both the real trigonometric and imaginary hyperbolic terms. -/
theorem section8_norm_sin_sq (z : ℂ) :
    ‖sin z‖^2 = (Real.sin z.re)^2 + (Real.sinh z.im)^2 := by
  rw [Complex.sq_norm, Complex.sin_eq, Complex.normSq_apply]
  simp only [add_re, mul_re, add_im, mul_im, sin_ofReal_re, cos_ofReal_re,
    sinh_ofReal_re, cosh_ofReal_re, sin_ofReal_im, cos_ofReal_im,
    sinh_ofReal_im, cosh_ofReal_im, I_re, I_im]
  have ht := Real.sin_sq_add_cos_sq z.re
  have hh := Real.cosh_sq z.im
  nlinarith [sq_nonneg (Real.sin z.re),sq_nonneg (Real.sinh z.im),
    mul_nonneg (sq_nonneg (Real.sinh z.im)) (sq_nonneg (Real.sin z.re))]

/-- Jordan's inequality controls the sine throughout a centered vertical strip. -/
theorem section8_centered_sine_lower {z : ℂ} (hz : |z.re| ≤ Real.pi/2) :
    (2/Real.pi)*‖z‖ ≤ ‖sin z‖ := by
  have hc : 0 ≤ 2/Real.pi := by positivity
  have hc1 : 2/Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr Real.two_le_pi
  have hx := Real.mul_abs_le_abs_sin hz
  have hy : (2/Real.pi)*|z.im| ≤ |Real.sinh z.im| := by
    rw [Real.abs_sinh]
    exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans
      (Real.self_le_sinh_iff.mpr (abs_nonneg _))
  have hx2 := pow_le_pow_left₀ (mul_nonneg hc (abs_nonneg z.re)) hx 2
  have hy2 := pow_le_pow_left₀ (mul_nonneg hc (abs_nonneg z.im)) hy 2
  simp only [mul_pow,sq_abs] at hx2 hy2
  have hn := Complex.sq_norm_sub_sq_re z
  have hs := section8_norm_sin_sq z
  nlinarith [norm_nonneg z,norm_nonneg (sin z),sq_nonneg ((2/Real.pi)*‖z‖-‖sin z‖)]

/-- The entire quarter-pi exterior has sine norm at least one half. -/
theorem section8_half_le_norm_sin {z : ℂ}
    (hz : ∀ n : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*n‖) : (1 : ℝ)/2 ≤ ‖sin z‖ := by
  obtain ⟨n,hn⟩ := exists_centered_real_part z
  let w := z-(Real.pi : ℂ)*n
  have hw : |w.re| ≤ Real.pi/2 := by simpa only [w,sub_re,mul_re,ofReal_re,intCast_re,
    ofReal_im,intCast_im,mul_zero,sub_zero] using hn
  have hsin : ‖sin w‖ = ‖sin z‖ := by
    dsimp only [w]
    rw [Complex.sin_sub]
    have hsn : sin ((Real.pi : ℂ)*n) = 0 := by simpa only [mul_comm] using Complex.sin_int_mul_pi n
    have hcn : ‖cos ((Real.pi : ℂ)*n)‖ = 1 := by
      rw [← Complex.ofReal_intCast,← Complex.ofReal_mul,← Complex.ofReal_cos,
        Complex.norm_real,Real.norm_eq_abs]
      simpa only [mul_comm] using Real.abs_cos_int_mul_pi n
    rw [hsn,mul_zero,sub_zero,norm_mul,hcn,mul_one]
  have hlow := section8_centered_sine_lower hw
  have hmul := mul_le_mul_of_nonneg_left (hz n) (show 0 ≤ 2/Real.pi by positivity)
  rw [show (2/Real.pi)*(Real.pi/4) = (1 : ℝ)/2 by field_simp; ring] at hmul
  rw [hsin] at hlow
  exact hmul.trans hlow

/-- The explicit factor four holds on the full original exterior, including the lower strip. -/
theorem section8_exp_abs_im_le_four_norm_sin {z : ℂ}
    (hz : ∀ n : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*n‖) :
    Real.exp |z.im| ≤ 4*‖sin z‖ := by
  by_cases h : Real.exp |z.im| ≤ 2
  · linarith [section8_half_le_norm_sin hz]
  · have hpos := Real.exp_pos |z.im|
    have hinv : Real.exp (-|z.im|) ≤ (1 : ℝ)/2 := by
      rw [Real.exp_neg]
      apply (inv_le_comm₀ hpos (by norm_num)).mpr
      norm_num
      exact le_of_not_ge h
    have hdiff := exp_abs_im_sub_exp_neg_abs_im_le_two_norm_sin z
    linarith

/-- The cosine has the standard exponential bound at every complex parameter. -/
theorem section8_norm_cos_le_exp_abs_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (exp (z*I)) (exp (-z*I))
  rw [← Complex.two_cos,norm_mul,norm_ofNat] at h
  simp only [norm_exp,mul_re,neg_re,neg_im,I_re,I_im,mul_zero,mul_one,zero_sub,neg_neg] at h
  have ha := Real.exp_le_exp.mpr (le_abs_self z.im)
  have hb := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith

/-- The literal two-step quotient bound used in the proof of Lemma 8.1. -/
theorem section8_exterior_sine_quotient (z : ℂ)
    (hz : ∀ n : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*n‖) :
    ‖cos z/sin z‖ ≤ Real.exp |z.im|/‖sin z‖ ∧
      Real.exp |z.im|/‖sin z‖ ≤ 4 := by
  have hs : 0 < ‖sin z‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2)
    (section8_half_le_norm_sin hz)
  constructor
  · rw [norm_div]
    exact div_le_div_of_nonneg_right (section8_norm_cos_le_exp_abs_im z) hs.le
  · exact (div_le_iff₀ hs).mpr (section8_exp_abs_im_le_four_norm_sin hz)

/-- The filled sine quotient has the literal cosine integral representation, including at zero. -/
theorem section8_freeSineQuotient_zero_integral (z : ℂ) :
    freeSineQuotient 0 z = ∫ s : ℝ in 0..1, cos ((s : ℂ)*z) := by
  by_cases hz : z = 0
  · subst z
    simp [freeSineQuotient, Complex.deriv_sin]
  · rw [freeSineQuotient_eq_div 0 z (by simpa using hz)]
    simpa only [Int.cast_zero, mul_zero, sub_zero, ofReal_one, mul_one,
      ofReal_zero, sin_zero, zero_div, mul_comm] using
      (integral_cos_mul_complex hz 0 1).symm

/-- Squaring removes the translating parity sign in the source's sinc integral. -/
theorem section8_freeSineQuotient_sq_integral (n : ℤ) (z : ℂ) :
    (freeSineQuotient n z)^2 =
      (∫ s : ℝ in 0..1, cos ((s : ℂ)*(z-(Real.pi : ℂ)*n)))^2 := by
  rw [freeSineQuotient_sq_translate, section8_freeSineQuotient_zero_integral]

end NLS.ZakharovShabat
