import NLS.ComplexAnalysis.SineFourierIntegral
import NLS.ComplexAnalysis.CosineNormEstimates

/-! # Exact cosine and mean Fourier integrals in the original normalization -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
namespace NLS.ComplexAnalysis

theorem integral_eq_periodOneCoefficient_zero (f : ℝ → ℂ) :
    (∫ s in (0 : ℝ)..1, f s) = periodOneCoefficient f 0 := by
  simp only [periodOneCoefficient,fourierCoeffOn_one,halfCoefficient,mul_zero,neg_zero,wave_zero,mul_one]
  ring

theorem integral_cos_nat_frequency (f : ℝ → ℂ) (hf : Continuous f) (k : ℕ) :
    (∫ s in (0 : ℝ)..1, cos ((k : ℂ)*Real.pi*((2*s-1 : ℝ) : ℂ))*f s) =
      (-1 : ℂ)^k*(periodOneCoefficient f (-(k : ℤ))+periodOneCoefficient f (k : ℤ))/2 := by
  have hcoeff (j : ℤ) : (∫ s in (0 : ℝ)..1, f s*wave (2*j) s) = periodOneCoefficient f (-j) := by
    simp only [periodOneCoefficient,fourierCoeffOn_one,halfCoefficient,mul_neg,neg_neg]
    ring
  have hcos : cos ((k : ℂ)*Real.pi) = (-1 : ℂ)^k := by
    have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi k)
    push_cast at h
    exact h
  have hpoint (s : ℝ) : cos ((k : ℂ)*Real.pi*((2*s-1 : ℝ) : ℂ)) =
      (-1 : ℂ)^k*(wave (2*(k : ℤ)) s+wave (2*(-(k : ℤ))) s)/2 := by
    have he : (k : ℂ)*Real.pi*((2*s-1 : ℝ) : ℂ) = 2*(k : ℂ)*Real.pi*s-(k : ℂ)*Real.pi := by push_cast; ring
    rw [he,cos_sub,Complex.sin_nat_mul_pi,mul_zero,add_zero,hcos,Complex.cos]
    have hp : exp ((2*(k : ℂ)*Real.pi*s)*I) = wave (2*(k : ℤ)) s := by
      unfold wave; congr 1; push_cast; ring
    have hm : exp (-(2*(k : ℂ)*Real.pi*s)*I) = wave (2*(-(k : ℤ))) s := by
      unfold wave; congr 1; push_cast; ring
    rw [hp,hm]
    ring
  calc
    _ = ((-1 : ℂ)^k/2)*∫ s in (0 : ℝ)..1,
        (f s*wave (2*(k : ℤ)) s+f s*wave (2*(-(k : ℤ))) s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [hpoint]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (f := fun s => f s*wave (2*(k : ℤ)) s)
        (g := fun s => f s*wave (2*(-(k : ℤ))) s)
        ((hf.mul (continuous_wave _)).intervalIntegrable 0 1)
        ((hf.mul (continuous_wave _)).intervalIntegrable 0 1),hcoeff,hcoeff,neg_neg]
      ring

theorem norm_cosine_frequency_integral_sub_le (f : ℝ → ℂ) (hf : Continuous f) (z : ℂ) (r : ℝ) :
    ‖∫ s in (0 : ℝ)..1, (cos (z*((2*s-1 : ℝ) : ℂ))-cos ((r : ℂ)*((2*s-1 : ℝ) : ℂ)))*f s‖ ≤
      Real.exp ‖z-r‖*‖z-r‖*(∫ s in (0 : ℝ)..1, ‖f s‖) := by
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖(cos (z*((2*s-1 : ℝ) : ℂ))-cos ((r : ℂ)*((2*s-1 : ℝ) : ℂ)))*f s‖ ≤
        (Real.exp ‖z-r‖*‖z-r‖)*‖f s‖ := by
    have ht : |2*s-1| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hd : ‖z*((2*s-1 : ℝ) : ℂ)-(r : ℂ)*((2*s-1 : ℝ) : ℂ)‖ ≤ ‖z-r‖ := by
      rw [← sub_mul,norm_mul,norm_real,Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) ht
    have h := norm_complex_cos_sub_le_exp (z*((2*s-1 : ℝ) : ℂ)) ((r : ℂ)*((2*s-1 : ℝ) : ℂ))
    simp only [mul_im,ofReal_im,mul_zero,zero_add,zero_mul,abs_zero,zero_add] at h
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (h.trans (mul_le_mul (Real.exp_le_exp.mpr hd) hd
      (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun s hs => hb s ⟨hs.1.le,hs.2⟩))
    ((continuous_const.mul hf.norm).intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_const_mul] using hi

end NLS.ComplexAnalysis
