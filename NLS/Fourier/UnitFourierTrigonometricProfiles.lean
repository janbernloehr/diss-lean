import NLS.Fourier.UnitIntervalFourierLinear
import NLS.Fourier.UnitIntervalWeakDerivative

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
namespace NLS.Fourier

/-- A literal period-one wave has exactly its original unit Fourier mode. -/
theorem unitFourierCoefficient_wave (j k : ℤ) :
    unitFourierCoefficient (wave (2*j)) k = if j = k then 1 else 0 := by
  unfold unitFourierCoefficient
  have he (x : ℝ) : wave (2*j) x * wave (-(2*k)) x = wave (2*(j-k)) x := by
    rw [←wave_add]
    congr 1
    ring
  simp only [he]
  change unitIntegral (2*(j-k)) = _
  rw [unitIntegral_even]
  simp only [sub_eq_zero]

/-- The two literal Fourier waves give the exact free energy-gradient
profile, in the period-one convention. -/
theorem twice_sin_sq_eq_waves (n : ℤ) (x : ℝ) :
    2*sin ((n : ℂ)*Real.pi*x)^2 = 1-(wave (2*n) x+wave (-(2*n)) x)/2 := by
  let z : ℂ := (n : ℂ)*Real.pi*x
  have hp : wave (2*n) x = exp ((2*z)*I) := by
    unfold wave
    congr 1
    push_cast
    dsimp only [z]
    ring
  have hm : wave (-(2*n)) x = exp (-(2*z)*I) := by
    unfold wave
    congr 1
    push_cast
    dsimp only [z]
    ring
  rw [hp,hm,Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
  have hc := Complex.cos_two_mul z
  have hs := Complex.sin_sq_add_cos_sq z
  change 2*sin z^2 = _
  linear_combination hc + 2*hs

/-- Complex constants commute with the actual unit Fourier integral. -/
theorem unitFourierCoefficient_const_mul_left (c : ℂ) (f : ℝ → ℂ) (k : ℤ) :
    unitFourierCoefficient (fun x => c*f x) k = c*unitFourierCoefficient f k := by
  unfold unitFourierCoefficient
  simp only [mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

/-- Exact Fourier coefficients of the free energy-gradient profile. -/
theorem unitFourierCoefficient_twice_sin_sq (n k : ℤ) :
    unitFourierCoefficient (fun x => 2*sin ((n : ℂ)*Real.pi*x)^2) k =
      (if k = 0 then 1 else 0) - ((if n = k then 1 else 0)+(if -n = k then 1 else 0))/2 := by
  have he : (fun x : ℝ => 2*sin ((n : ℂ)*Real.pi*x)^2) =
      (fun x => (1 : ℂ)+(-1/2)*wave (2*n) x+(-1/2)*wave (2*(-n)) x) := by
    funext x
    rw [twice_sin_sq_eq_waves,show 2*(-n) = -(2*n) by ring]
    ring
  rw [he,unitFourierCoefficient_add,unitFourierCoefficient_add,
    unitFourierCoefficient_const,unitFourierCoefficient_const_mul_left,
    unitFourierCoefficient_const_mul_left,unitFourierCoefficient_wave,unitFourierCoefficient_wave]
  · ring
  · exact continuous_const.intervalIntegrable 0 1
  · exact ((continuous_wave _).const_mul _).intervalIntegrable 0 1
  · exact (continuous_const.add ((continuous_wave _).const_mul _)).intervalIntegrable 0 1
  · exact ((continuous_wave _).const_mul _).intervalIntegrable 0 1

/-- The free mixed gradient is exactly the antisymmetric pair of waves. -/
theorem cos_mul_sin_eq_waves (n : ℤ) (x : ℝ) :
    cos ((n : ℂ)*Real.pi*x)*sin ((n : ℂ)*Real.pi*x) =
      (wave (2*n) x-wave (-(2*n)) x)/(4*I) := by
  let z : ℂ := (n : ℂ)*Real.pi*x
  have hp : wave (2*n) x = exp ((2*z)*I) := by
    unfold wave
    congr 1
    push_cast
    dsimp only [z]
    ring
  have hm : wave (-(2*n)) x = exp (-(2*z)*I) := by
    unfold wave
    congr 1
    push_cast
    dsimp only [z]
    ring
  rw [hp,hm,Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg,Complex.sin_two_mul]
  change cos z*sin z = _
  field_simp
  ring

/-- Exact signed Fourier coefficients of the free norming-gradient profile,
with any constant divisor (including zero). -/
theorem unitFourierCoefficient_cos_mul_sin_div (n k : ℤ) (c : ℂ) :
    unitFourierCoefficient (fun x => cos ((n : ℂ)*Real.pi*x)*sin ((n : ℂ)*Real.pi*x)/c) k =
      ((if n = k then 1 else 0)-(if -n = k then 1 else 0))/(4*I*c) := by
  have he : (fun x : ℝ => cos ((n : ℂ)*Real.pi*x)*sin ((n : ℂ)*Real.pi*x)/c) =
      (fun x => (4*I*c)⁻¹*(wave (2*n) x-wave (2*(-n)) x)) := by
    funext x
    rw [cos_mul_sin_eq_waves,show 2*(-n) = -(2*n) by ring,div_div]
    ring
  rw [he,unitFourierCoefficient_const_mul_left,unitFourierCoefficient_sub,
    unitFourierCoefficient_wave,unitFourierCoefficient_wave]
  · ring
  · exact (continuous_wave _).intervalIntegrable 0 1
  · exact (continuous_wave _).intervalIntegrable 0 1

end NLS.Fourier
