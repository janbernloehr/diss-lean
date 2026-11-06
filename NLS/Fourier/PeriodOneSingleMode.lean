import NLS.Fourier.PeriodOneCoefficients
import NLS.Fourier.DistributionModulation

/-! # Actual smooth unit-period single Fourier modes -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace NLS.Fourier

/-- The physical wave at twice an integer has exactly the unit-period single coefficient. -/
theorem periodOneCoefficient_wave_even (k n : ℤ) :
    periodOneCoefficient (wave (2*k)) n = Finsupp.single k (1 : ℂ) n := by
  have he : wave (2*k) = polynomial (Finsupp.single k (1 : ℂ)) := by
    funext x
    simp [polynomial]
  rw [he,periodOneCoefficient,fourierCoeffOn_one,halfCoefficient_polynomial_even]
  ring

/-- Original even physical waves have period one. -/
theorem periodic_wave_even (k : ℤ) : Function.Periodic (wave (2*k)) 1 := by
  intro x
  rw [wave_add_argument]
  simpa using congrArg (fun z : ℂ => wave (2*k) x*z) (wave_even_at_one k)

end NLS.Fourier
