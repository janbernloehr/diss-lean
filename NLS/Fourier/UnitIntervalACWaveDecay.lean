import NLS.Fourier.UnitIntervalCoefficientDecay

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.Fourier



/-- Actual period-two Fourier waves integrated on the physical unit interval
have inverse-bracket decay under absolute continuity, with both boundary
terms retained. Matching endpoints and C1 regularity are not required. -/
theorem norm_unitIntegral_mul_wave_le_bracket_of_ac
    (f : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfi : IntervalIntegrable (deriv f) volume 0 1)
    (A D : ℝ) (hA : 0≤A) (hD : 0≤D)
    (hb : ∀ t∈Icc (0 : ℝ) 1, ‖f t‖≤A)
    (hd : (∫ t in (0 : ℝ)..1, ‖deriv f t‖)≤D) (n : ℤ) :
    ‖∫ t in (0 : ℝ)..1, f t*wave n t‖≤(2*A+D)/(1+|(n : ℝ)|) := by
  by_cases hn : n=0
  · subst n
    simp only [wave_zero,mul_one,Int.cast_zero,abs_zero,add_zero,div_one]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (fun t ht => hb t (by
        have ht' : t∈Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ)≤1)] using ht
        exact ⟨ht'.1.le,ht'.2⟩))
    simp only [sub_zero,abs_one,mul_one] at h
    linarith
  · let c : ℂ := -(I*(Real.pi : ℂ)*(n : ℂ))/2
    have hc : c≠0 := div_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
        (by exact_mod_cast hn))) (by norm_num)
    have he : (∫ t in (0 : ℝ)..1, f t*wave n t)=exp (-c)*oscillatoryIntegral c 1 f := by
      rw [oscillatoryIntegral,← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      unfold oscillatoryKernel wave
      dsimp only []
      rw [← mul_assoc,← Complex.exp_add]
      rw [mul_comm (f t)]
      congr 2
      dsimp only [c]
      push_cast
      ring
    have hcre : c.re=0 := by simp [c,mul_re,mul_im]
    have hcn : ‖c‖=Real.pi*|(n : ℝ)|/2 := by
      simp [c,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    have hn1 : 1≤|(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hvar : ‖f 0‖+‖f 1‖+(∫ t in (0 : ℝ)..1, ‖deriv f t‖)≤2*A+D := by
      linarith [hb 0 (by simp),hb 1 (by simp)]
    rw [he,norm_mul,Complex.norm_exp,neg_re,hcre,neg_zero,Real.exp_zero,one_mul]
    have h := norm_oscillatoryIntegral_le c hc 1 (by norm_num) f hf hfi
    simp only [hcre,abs_zero,zero_mul,Real.exp_zero,one_mul,hcn] at h
    have hden : 2*(Real.pi*|(n : ℝ)|/2)=Real.pi*|(n : ℝ)| := by ring
    rw [hden] at h
    exact (h.trans (div_le_div_of_nonneg_right hvar (by positivity))).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [Real.two_le_pi]))

end NLS.Fourier
