import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # The sign of a square near a nonzero imaginary value -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.ComplexAnalysis

theorem re_sq_neg_of_near_imaginary (z : ℂ) (t : ℝ) (ht : 0 < t)
    (h : ‖z-I*(t : ℂ)‖ ≤ t/4) : (z^2).re < 0 := by
  have hre := (abs_re_le_norm (z-I*(t : ℂ))).trans h
  have him := (abs_im_le_norm (z-I*(t : ℂ))).trans h
  simp only [sub_re,mul_re,I_re,ofReal_re,zero_mul,I_im,ofReal_im,mul_zero,sub_self,sub_zero] at hre
  simp only [sub_im,mul_im,I_re,ofReal_im,zero_mul,I_im,ofReal_re,one_mul,zero_add] at him
  have hra := abs_le.mp hre
  have hia := abs_le.mp him
  have hs : z.re^2 ≤ (t/4)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ t/4-z.re by linarith) (show 0 ≤ t/4+z.re by linarith)]
  have hsi : (3*t/4)^2 ≤ z.im^2 := by
    apply (sq_le_sq₀ (by positivity) (by linarith)).mpr
    linarith
  simp only [pow_two,mul_re]
  nlinarith

/-- The real part of a two-endpoint factorization is nonnegative
between the real endpoints when the unit square has negative real part. -/
theorem re_two_endpoint_square_nonneg (g H : ℂ → ℂ) (l u x : ℝ)
    (hx : x ∈ Set.Icc l u)
    (hfactor : g (x : ℂ) = ((x : ℂ)-l)*((x : ℂ)-u)*(H (x : ℂ))^2)
    (hH : ((H (x : ℂ))^2).re ≤ 0) : 0 ≤ (g (x : ℂ)).re := by
  rw [hfactor]
  have hp : (x-l)*(x-u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2)
  have hh := mul_nonneg_of_nonpos_of_nonpos hp hH
  simpa only [mul_re,mul_im,sub_re,ofReal_re,sub_im,ofReal_im,sub_self,mul_zero,zero_mul,zero_add,sub_zero] using hh

end NLS.ComplexAnalysis
