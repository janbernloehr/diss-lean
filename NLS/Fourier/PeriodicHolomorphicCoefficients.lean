import NLS.Fourier.PeriodOneCoefficients
import NLS.FunctionalAnalysis.RectangleIntegral

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
namespace NLS.Fourier

/-- The period-one Fourier wave evaluated at a complex argument. -/
def complexPeriodOneWave (n : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (2*(Real.pi:ℂ)*I*(n:ℂ)*z)

/-- Complex period-one waves retain their exact period at all heights. -/
theorem complexPeriodOneWave_periodic (n : ℤ) :
    Function.Periodic (complexPeriodOneWave n) 1 := by
  intro z
  have he : 2*(Real.pi:ℂ)*I*(n:ℂ)*(z+1) =
      2*(Real.pi:ℂ)*I*(n:ℂ)*z+(n:ℂ)*(2*Real.pi*I) := by ring
  simp only [complexPeriodOneWave,he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]

/-- A horizontal translation gives the exact real exponential Fourier multiplier. -/
theorem complexPeriodOneWave_horizontal (n : ℤ) (x y : ℝ) :
    complexPeriodOneWave n ((x:ℂ)+y*I) =
      (Real.exp (-2*Real.pi*y*(n:ℝ)):ℂ)*complexPeriodOneWave n x := by
  have he : 2*(Real.pi:ℂ)*I*(n:ℂ)*((x:ℂ)+y*I) =
      ((-2*Real.pi*y*(n:ℝ):ℝ):ℂ)+(Real.pi:ℂ)*I*(2*(n:ℂ))*x := by
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  simp only [complexPeriodOneWave,he,Complex.exp_add,← Complex.ofReal_exp]
  congr 2
  ring

/-- Cauchy's rectangle theorem cancels the vertical edges of a periodic integrand. -/
theorem horizontal_integral_eq_of_periodic (f : ℂ → ℂ)
    (hf : Function.Periodic f 1) (y₀ y₁ : ℝ)
    (hd : DifferentiableOn ℂ f (uIcc (0:ℝ) 1 ×ℂ uIcc y₀ y₁)) :
    (∫ x : ℝ in 0..1, f ((x:ℂ)+y₀*I)) =
      ∫ x : ℝ in 0..1, f ((x:ℂ)+y₁*I) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (⟨0,y₀⟩:ℂ) (⟨1,y₁⟩:ℂ) hd
  have hp (t : ℝ) : f ((1:ℂ)+t*I) = f ((0:ℂ)+t*I) := by
    simpa only [add_comm (1:ℂ),zero_add] using hf ((t:ℂ)*I)
  dsimp only at h
  simp only [Complex.ofReal_zero,Complex.ofReal_one,hp] at h
  linear_combination h

/-- The actual unit-interval Fourier integral uses the complex wave at height zero. -/
theorem periodOneCoefficient_eq_complex_integral (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient f n =
      ∫ x : ℝ in 0..1, f x*complexPeriodOneWave (-n) x := by
  rw [periodOneCoefficient,fourierCoeffOn_one,halfCoefficient,← mul_assoc]
  norm_num only [mul_one_div_cancel,one_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  congr 1
  unfold wave complexPeriodOneWave
  push_cast
  congr 1
  ring

/-- Holomorphic periodic functions transport their actual Fourier integrals by
exp(-2*pi*n*y), with the original physical unit-period normalization. -/
theorem periodOneCoefficient_horizontal (f : ℂ → ℂ)
    (hf : Function.Periodic f 1) (y : ℝ)
    (hd : DifferentiableOn ℂ f (uIcc (0:ℝ) 1 ×ℂ uIcc (0:ℝ) y)) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => f ((x:ℂ)+y*I)) n =
      (Real.exp (-2*Real.pi*y*(n:ℝ)):ℂ)*periodOneCoefficient (fun x : ℝ => f x) n := by
  let g : ℂ → ℂ := fun z => f z*complexPeriodOneWave (-n) z
  have hp : Function.Periodic g 1 := by
    intro z
    simp only [g,hf z,complexPeriodOneWave_periodic (-n) z]
  have hg : DifferentiableOn ℂ g (uIcc (0:ℝ) 1 ×ℂ uIcc (0:ℝ) y) := by
    apply hd.mul
    unfold complexPeriodOneWave
    fun_prop
  have h := horizontal_integral_eq_of_periodic g hp 0 y hg
  have h0 : (∫ x : ℝ in 0..1, g ((x:ℂ)+(0:ℝ)*I)) =
      periodOneCoefficient (fun x : ℝ => f x) n := by
    simp only [g,Complex.ofReal_zero,zero_mul,add_zero,periodOneCoefficient_eq_complex_integral]
  have hy : (∫ x : ℝ in 0..1, g ((x:ℂ)+y*I)) =
      (Real.exp (2*Real.pi*y*(n:ℝ)):ℂ)*
        periodOneCoefficient (fun x : ℝ => f ((x:ℂ)+y*I)) n := by
    rw [periodOneCoefficient_eq_complex_integral,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    simp only [g,complexPeriodOneWave_horizontal,Int.cast_neg]
    rw [show -2*Real.pi*y* -(n:ℝ) = 2*Real.pi*y*(n:ℝ) by ring]
    ring
  rw [h0,hy] at h
  rw [h,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp only [show -2*Real.pi*y*(n:ℝ)+2*Real.pi*y*(n:ℝ) = 0 by ring,
    Real.exp_zero,Complex.ofReal_one,one_mul]

end NLS.Fourier
