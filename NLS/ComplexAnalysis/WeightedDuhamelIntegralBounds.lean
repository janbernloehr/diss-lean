import NLS.ComplexAnalysis.DuhamelIntegralBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



theorem norm_trig_mul_real_le_exp (z : ℂ) (t : ℝ) (ht : 0≤t) :
    ‖cos (z*t)‖≤Real.exp (|z.im| *t) ∧ ‖sin (z*t)‖≤Real.exp (|z.im| *t) := by
  have hi : |(z*t).im|=|z.im| *t := by
    simp only [mul_im,ofReal_im,ofReal_re,mul_zero,zero_add,abs_mul,abs_of_nonneg ht]
  exact ⟨by simpa only [hi] using norm_complex_cos_le_exp_im (z*t),
    by simpa only [hi] using norm_complex_sin_le_exp_im (z*t)⟩

theorem exp_mul_cancel_weight (a b : ℝ) : Real.exp a*(Real.exp (-a)*b)=b := by
  rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

theorem le_exp_mul_of_weight_le (a b C : ℝ) (h : Real.exp (-a)*b≤C) :
    b≤Real.exp a*C := by
  simpa only [exp_mul_cancel_weight] using mul_le_mul_of_nonneg_left h (Real.exp_pos a).le

/-- Exponential weights cancel along the Volterra triangle, so the
smallness condition need not depend exponentially on the imaginary frequency. -/
theorem norm_sine_duhamel_integral_le_weighted (q u : ℝ → ℂ) (z : ℂ) (B t : ℝ)
    (hq : Continuous q) (ht : 0≤t)
    (hu : ∀ s∈Icc 0 t, ‖u s‖≤Real.exp (|z.im| *s)*B) :
    ‖∫ s in (0 : ℝ)..t,sin (z*((t-s : ℝ) : ℂ))/z*q s*u s‖≤
      (Real.exp (|z.im| *t)/‖z‖*B)*(∫ s in (0 : ℝ)..t,‖q s‖) := by
  have hb (s : ℝ) (hs : s∈Icc (0 : ℝ) t) :
      ‖sin (z*((t-s : ℝ) : ℂ))/z*q s*u s‖≤
        (Real.exp (|z.im| *t)/‖z‖*B)*‖q s‖ := by
    have htr := (norm_trig_mul_real_le_exp z (t-s) (sub_nonneg.mpr hs.2)).2
    rw [norm_mul,norm_mul,norm_div]
    have hh := mul_le_mul (div_le_div_of_nonneg_right htr (norm_nonneg z))
      (hu s hs) (norm_nonneg _) (by positivity : 0≤Real.exp (|z.im| *(t-s))/‖z‖)
    have he : (Real.exp (|z.im| *(t-s))/‖z‖)*(Real.exp (|z.im| *s)*B)=
        Real.exp (|z.im| *t)/‖z‖*B := by
      calc
        _ = (Real.exp (|z.im| *(t-s))*Real.exp (|z.im| *s))/‖z‖*B := by ring
        _ = _ := by rw [← Real.exp_add,show |z.im| *(t-s)+|z.im| *s=|z.im| *t by ring]
    rw [he] at hh
    nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg (q s))]
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
    (Filter.Eventually.of_forall (fun s hs => hb s ⟨hs.1.le,hs.2⟩))
    ((continuous_const.mul hq.norm).intervalIntegrable 0 t)
  simpa only [intervalIntegral.integral_const_mul] using hi

end NLS.ComplexAnalysis
