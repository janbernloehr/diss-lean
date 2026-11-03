import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal

namespace NLS.ComplexAnalysis



theorem norm_complex_cos_le_exp_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  have hp : ‖exp (z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [mul_re,I_re,I_im,mul_zero,mul_one,zero_sub] using neg_le_abs z.im
  have hm : ‖exp (-z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [mul_re,I_re,I_im,neg_re,neg_im,mul_zero,mul_one,zero_sub,neg_neg] using le_abs_self z.im
  calc
    _ = ‖exp (z*I)+exp (-z*I)‖/2 := by rw [Complex.cos,norm_div];norm_num
    _ ≤ (Real.exp |z.im|+Real.exp |z.im|)/2 :=
      div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add hp hm)) (by norm_num)
    _ = _ := by ring

theorem norm_complex_sin_le_exp_im (z : ℂ) : ‖sin z‖ ≤ Real.exp |z.im| := by
  have hp : ‖exp (z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [mul_re,I_re,I_im,mul_zero,mul_one,zero_sub] using neg_le_abs z.im
  have hm : ‖exp (-z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [mul_re,I_re,I_im,neg_re,neg_im,mul_zero,mul_one,zero_sub,neg_neg] using le_abs_self z.im
  calc
    _ = ‖exp (-z*I)-exp (z*I)‖/2 := by rw [Complex.sin,norm_div,norm_mul,norm_I,mul_one];norm_num
    _ ≤ (Real.exp |z.im|+Real.exp |z.im|)/2 :=
      div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hm hp)) (by norm_num)
    _ = _ := by ring

theorem norm_trig_mul_real_le (z : ℂ) (H r : ℝ) (hH : |z.im| ≤ H) (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖cos (z*r)‖ ≤ Real.exp H ∧ ‖sin (z*r)‖ ≤ Real.exp H := by
  have him : |(z*r).im| ≤ H := by
    simp only [mul_im,ofReal_im,ofReal_re,mul_zero,zero_add,abs_mul,abs_of_nonneg hr.1]
    exact (mul_le_of_le_one_right (abs_nonneg z.im) hr.2).trans hH
  exact ⟨(norm_complex_cos_le_exp_im _).trans (Real.exp_le_exp.mpr him),
    (norm_complex_sin_le_exp_im _).trans (Real.exp_le_exp.mpr him)⟩

theorem norm_sine_duhamel_integral_le (q u : ℝ → ℂ) (z : ℂ) (H B t : ℝ)
    (hq : Continuous q) (hH : |z.im| ≤ H) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : ∀ s ∈ Icc 0 t, ‖u s‖ ≤ B) :
    ‖∫ s in (0 : ℝ)..t,sin (z*((t-s : ℝ) : ℂ))/z*q s*u s‖ ≤
      (Real.exp H/‖z‖*B)*(∫ s in (0 : ℝ)..t,‖q s‖) := by
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      ‖sin (z*((t-s : ℝ) : ℂ))/z*q s*u s‖ ≤ (Real.exp H/‖z‖*B)*‖q s‖ := by
    have htr := (norm_trig_mul_real_le z H (t-s) hH ⟨by linarith [hs.2],by linarith [hs.1,ht.2]⟩).2
    rw [norm_mul,norm_mul,norm_div]
    have h1 := div_le_div_of_nonneg_right htr (norm_nonneg z)
    have h2 := mul_le_mul h1 (hu s hs) (norm_nonneg _) (by positivity : 0 ≤ Real.exp H/‖z‖)
    nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg (q s))]
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht.1
    (Filter.Eventually.of_forall (fun s hs => hb s ⟨hs.1.le,hs.2⟩))
    ((continuous_const.mul hq.norm).intervalIntegrable 0 t)
  simpa only [intervalIntegral.integral_const_mul] using hi

theorem norm_cosine_duhamel_integral_le (q u : ℝ → ℂ) (z : ℂ) (H B t : ℝ)
    (hq : Continuous q) (hH : |z.im| ≤ H) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : ∀ s ∈ Icc 0 t, ‖u s‖ ≤ B) :
    ‖∫ s in (0 : ℝ)..t,cos (z*((t-s : ℝ) : ℂ))*q s*u s‖ ≤
      (Real.exp H*B)*(∫ s in (0 : ℝ)..t,‖q s‖) := by
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      ‖cos (z*((t-s : ℝ) : ℂ))*q s*u s‖ ≤ (Real.exp H*B)*‖q s‖ := by
    have htr := (norm_trig_mul_real_le z H (t-s) hH ⟨by linarith [hs.2],by linarith [hs.1,ht.2]⟩).1
    rw [norm_mul,norm_mul]
    have h := mul_le_mul htr (hu s hs) (norm_nonneg _) (Real.exp_nonneg H)
    nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (q s))]
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht.1
    (Filter.Eventually.of_forall (fun s hs => hb s ⟨hs.1.le,hs.2⟩))
    ((continuous_const.mul hq.norm).intervalIntegrable 0 t)
  simpa only [intervalIntegral.integral_const_mul] using hi

end NLS.ComplexAnalysis
