import NLS.KdV.ClassicalHillFreeVariation

/-! Exact Fourier kernels of the physical Dirichlet characteristic and
norming terminal derivative at each free positive Hill eigenvalue. -/
noncomputable section
open scoped Real
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

theorem complex_cos_nat_pi (n : ℕ) : cos (π*n) = (-1:ℂ)^n := by
  have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
  simpa only [Complex.ofReal_cos,Complex.ofReal_mul,Complex.ofReal_natCast,
    Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one,mul_comm] using h

theorem complex_sin_nat_pi (n : ℕ) : sin (π*n) = 0 := by
  simpa only [mul_comm] using Complex.sin_nat_mul_pi n

theorem fderiv_classicalHillDirichlet_free_fourier (h : Curve ℂ) (n : ℕ+ ) :
    (fderiv ℂ (fun q => classicalHillDirichlet q ((π*n)^2)) 0) h =
      -(-1:ℂ)^(n:ℕ)/(π*n)^2 *
        ∫ s in (0:ℝ)..1, extend h s * sin (π*n*(s:ℂ))^2 := by
  have hz : (π:ℂ)*n ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    (by exact_mod_cast n.ne_zero)
  rw [fderiv_classicalHillDirichlet_free h (π*n) hz,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [mul_sub, mul_one, Complex.sin_sub,complex_sin_nat_pi,complex_cos_nat_pi]
  field_simp [hz]
  ring

theorem fderiv_classicalHillDirichletTerminal_free_fourier (h : Curve ℂ) (n : ℕ+ ) :
    (fderiv ℂ (fun q => classicalHillDirichletTerminal q ((π*n)^2)) 0) h =
      (-1:ℂ)^(n:ℕ)/(2*(π*n)) *
        ∫ s in (0:ℝ)..1, extend h s * sin (2*(π*n)*(s:ℂ)) := by
  have hz : (π:ℂ)*n ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    (by exact_mod_cast n.ne_zero)
  rw [fderiv_classicalHillDirichletTerminal_free h (π*n) hz,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [mul_sub, mul_one, Complex.cos_sub,complex_sin_nat_pi,complex_cos_nat_pi]
  rw [show 2*((π:ℂ)*n)*(s:ℂ)=2*(π*n*(s:ℂ)) by ring,Complex.sin_two_mul]
  field_simp [hz]
  ring

end NLS.KdV
