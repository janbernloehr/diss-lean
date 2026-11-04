import NLS.ComplexAnalysis.DuhamelIntegralBounds

/-! # Exponentially weighted scalar Duhamel estimates -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- The exact time weight retains the physical exponential growth. -/
theorem norm_trig_mul_real_weighted_le (z : ℂ) (H t : ℝ) (hH : |z.im|≤H) (ht : 0≤t) :
    ‖cos (z*t)‖≤Real.exp (H*t) ∧ ‖sin (z*t)‖≤Real.exp (H*t) := by
  have him : |(z*t).im|≤H*t := by
    simp only [mul_im,ofReal_im,ofReal_re,mul_zero,zero_add,abs_mul,abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_right hH ht
  exact ⟨(norm_complex_cos_le_exp_im _).trans (Real.exp_le_exp.mpr him),
    (norm_complex_sin_le_exp_im _).trans (Real.exp_le_exp.mpr him)⟩

/-- The weights at times t-s and s multiply to the weight at t. Thus the
Volterra coefficient is the potential mass divided by frequency, without an
additional exponential in the smallness condition. -/
theorem norm_sine_duhamel_integral_weighted_le (q u : ℝ → ℂ) (z : ℂ) (H B t : ℝ)
    (hq : Continuous q) (hH : |z.im|≤H) (ht : 0≤t)
    (hu : ∀ s∈Icc 0 t, ‖u s‖≤Real.exp (H*s)*B) :
    ‖∫ s in (0 : ℝ)..t,sin (z*((t-s : ℝ) : ℂ))/z*q s*u s‖≤
      (Real.exp (H*t)/‖z‖*B)*(∫ s in (0 : ℝ)..t,‖q s‖) := by
  have hb (s : ℝ) (hs : s∈Icc (0 : ℝ) t) :
      ‖sin (z*((t-s : ℝ) : ℂ))/z*q s*u s‖≤(Real.exp (H*t)/‖z‖*B)*‖q s‖ := by
    have htr := (norm_trig_mul_real_weighted_le z H (t-s) hH (sub_nonneg.mpr hs.2)).2
    rw [norm_mul,norm_mul,norm_div]
    have h1 := div_le_div_of_nonneg_right htr (norm_nonneg z)
    have h2 := mul_le_mul h1 (hu s hs) (norm_nonneg _) (by positivity : 0≤Real.exp (H*(t-s))/‖z‖)
    calc
      _ ≤ (Real.exp (H*(t-s))/‖z‖*(Real.exp (H*s)*B))*‖q s‖ := by
        nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg (q s))]
      _ = _ := by
        rw [show Real.exp (H*(t-s))/‖z‖*(Real.exp (H*s)*B)=
          (Real.exp (H*(t-s))*Real.exp (H*s))/‖z‖*B by ring,
          ← Real.exp_add,show H*(t-s)+H*s=H*t by ring]
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
    (Filter.Eventually.of_forall (fun s hs => hb s ⟨hs.1.le,hs.2⟩))
    ((continuous_const.mul hq.norm).intervalIntegrable 0 t)
  simpa only [intervalIntegral.integral_const_mul] using hi

end NLS.ComplexAnalysis
