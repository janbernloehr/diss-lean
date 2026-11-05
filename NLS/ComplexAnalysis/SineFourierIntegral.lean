import NLS.Fourier.PeriodOneCoefficients

/-! # The exact Fourier leading term of the Hill terminal sine integral -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
namespace NLS.ComplexAnalysis

theorem integral_sin_nat_frequency (f : ℝ → ℂ) (hf : Continuous f) (k : ℕ) :
    (∫ s in (0 : ℝ)..1, sin ((k : ℂ)*Real.pi*((2*s-1 : ℝ) : ℂ))*f s) =
      (-1 : ℂ)^k*(periodOneCoefficient f (-(k : ℤ))-periodOneCoefficient f (k : ℤ))/(2*I) := by
  have hcoeff (j : ℤ) : (∫ s in (0 : ℝ)..1, f s*wave (2*j) s) = periodOneCoefficient f (-j) := by
    simp only [periodOneCoefficient,fourierCoeffOn_one,halfCoefficient,mul_neg,neg_neg]
    ring
  have hcos : cos ((k : ℂ)*Real.pi) = (-1 : ℂ)^k := by
    have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi k)
    push_cast at h
    exact h
  have hpoint (s : ℝ) : sin ((k : ℂ)*Real.pi*((2*s-1 : ℝ) : ℂ)) =
      (-1 : ℂ)^k*(wave (2*(k : ℤ)) s-wave (2*(-(k : ℤ))) s)/(2*I) := by
    have he : (k : ℂ)*Real.pi*((2*s-1 : ℝ) : ℂ) = 2*(k : ℂ)*Real.pi*s-(k : ℂ)*Real.pi := by push_cast; ring
    rw [he,sin_sub,Complex.sin_nat_mul_pi,mul_zero,sub_zero,hcos,Complex.sin]
    have hp : exp ((2*(k : ℂ)*Real.pi*s)*I) = wave (2*(k : ℤ)) s := by
      unfold wave; congr 1; push_cast; ring
    have hm : exp (-(2*(k : ℂ)*Real.pi*s)*I) = wave (2*(-(k : ℤ))) s := by
      unfold wave; congr 1; push_cast; ring
    rw [hp,hm]
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  calc
    _ = ((-1 : ℂ)^k/(2*I))*∫ s in (0 : ℝ)..1,
        (f s*wave (2*(k : ℤ)) s-f s*wave (2*(-(k : ℤ))) s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [hpoint]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (f := fun s => f s*wave (2*(k : ℤ)) s)
        (g := fun s => f s*wave (2*(-(k : ℤ))) s)
        ((hf.mul (continuous_wave _)).intervalIntegrable 0 1)
        ((hf.mul (continuous_wave _)).intervalIntegrable 0 1),hcoeff,hcoeff,neg_neg]
      ring

end NLS.ComplexAnalysis
