import NLS.Fourier.IntervalBilinearParseval
import NLS.Fourier.PeriodOneCoefficients

/-! # Exact Fourier coefficients on the pi lattice -/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.Fourier

/-- The oscillatory density integral on the pi lattice is the exact
unit-period Fourier coefficient, with no normalization factor. -/
theorem integral_pi_lattice_eq_periodOneCoefficient (f : ℝ → ℂ) (n : ℤ) :
    (∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n)*x)) = periodOneCoefficient f n := by
  change _ = fourierCoeffOn (by norm_num : (0:ℝ) < 1) f n
  rw [← unitFourierCoefficient_eq_fourierCoeffOn]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x _
  have he : exp (-2*I*((Real.pi:ℂ)*n)*(x:ℂ)) = wave (-(2*n)) x := by
    unfold wave
    apply congrArg exp
    push_cast
    ring
  exact congrArg (fun c : ℂ => f x*c) he

end NLS.Fourier
