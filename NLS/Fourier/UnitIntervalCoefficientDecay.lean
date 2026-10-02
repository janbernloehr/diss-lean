import NLS.Fourier.UnitIntervalEnergyBound
import NLS.ComplexAnalysis.OscillatoryIntegralParts

/-! # Unit-interval Fourier decay without matching endpoints

Integration by parts retains both boundary values. A C¹ function with
bounded value and derivative has a common inverse-bracket bound on all
its actual unit-interval coefficients, including frequency zero.
-/

noncomputable section
open Set Complex MeasureTheory NLS.ComplexAnalysis
namespace NLS.Fourier

/-- The unit Fourier integral is the oscillatory integral with its constant phase removed. -/
theorem unitIntervalFourierCoefficient_eq_oscillatory (f : ℝ → ℂ) (n : ℤ) :
    intervalFourierCoefficient 1 f n =
      exp (-I*(Real.pi : ℂ)*(n : ℂ))*oscillatoryIntegral (I*(Real.pi : ℂ)*(n : ℂ)) 1 f := by
  simp only [intervalFourierCoefficient,div_one,Complex.ofReal_one,one_mul]
  rw [oscillatoryIntegral,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [mul_comm (f s),← mul_assoc]
  unfold wave oscillatoryKernel
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The nonzero-frequency coefficient bound includes both endpoint terms. -/
theorem norm_unitIntervalFourierCoefficient_le_variation
    (f : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfi : IntervalIntegrable (deriv f) volume 0 1) (n : ℤ) (hn : n ≠ 0) :
    ‖intervalFourierCoefficient 1 f n‖ ≤
      (‖f 0‖+‖f 1‖+∫ t in (0 : ℝ)..1, ‖deriv f t‖)/(2*Real.pi*|(n : ℝ)|) := by
  rw [unitIntervalFourierCoefficient_eq_oscillatory,norm_mul]
  have hc : I*(Real.pi : ℂ)*(n : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero I_ne_zero (by exact_mod_cast Real.pi_ne_zero)) (by exact_mod_cast hn)
  have h := norm_oscillatoryIntegral_le (I*(Real.pi : ℂ)*(n : ℂ)) hc 1 (by norm_num) f hf hfi
  simpa [Complex.norm_exp,Complex.mul_re,Complex.mul_im,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_assoc] using h

/-- The zero-frequency-safe inverse-bracket estimate from separate C¹ bounds. -/
theorem norm_unitIntervalFourierCoefficient_le_bracket
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ D) (n : ℤ) :
    ‖intervalFourierCoefficient 1 f n‖ ≤ (2*A+D)/(1+|(n : ℝ)|) := by
  have hder := (contDiff_one_iff_deriv.mp hf).2
  by_cases hn : n = 0
  · subst n
    simp only [intervalFourierCoefficient,div_one,Complex.ofReal_one,one_mul,
      neg_zero,wave_zero,mul_one,Int.cast_zero,abs_zero,add_zero,div_one]
    have h : ‖∫ t in (0 : ℝ)..1, f t‖ ≤ A := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (fun t ht => hb t (by
          have ht' : t ∈ Ioc (0 : ℝ) 1 := by
            simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
          exact ⟨ht'.1.le,ht'.2⟩))
      simpa using hi
    linarith
  · have hi : (∫ t in (0 : ℝ)..1, ‖deriv f t‖) ≤ D := by
      have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
        (hder.norm.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1) hd
      simpa using h
    have hvar : ‖f 0‖+‖f 1‖+(∫ t in (0 : ℝ)..1, ‖deriv f t‖) ≤ 2*A+D := by
      linarith [hb 0 (by simp),hb 1 (by simp)]
    have hn1 : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    calc
      _ ≤ (‖f 0‖+‖f 1‖+(∫ t in (0 : ℝ)..1, ‖deriv f t‖))/(2*Real.pi*|(n : ℝ)|) :=
        norm_unitIntervalFourierCoefficient_le_variation f hf.contDiffOn.absolutelyContinuousOnInterval
          (hder.intervalIntegrable 0 1) n hn
      _ ≤ (2*A+D)/(2*Real.pi*|(n : ℝ)|) := div_le_div_of_nonneg_right hvar (by positivity)
      _ ≤ (2*A+D)/(1+|(n : ℝ)|) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [Real.two_le_pi])

end NLS.Fourier
