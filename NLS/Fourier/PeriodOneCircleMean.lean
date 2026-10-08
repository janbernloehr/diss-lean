import NLS.Fourier.PeriodOneSobolev
import NLS.Fourier.IntervalBilinearParseval

/-! # The bounded mean of continuous unit-period fields -/
noncomputable section
open MeasureTheory
namespace NLS.Fourier

/-- The zero Fourier coefficient is a bounded physical mean. -/
def periodOneCircleMean : C(AddCircle (2:ℝ),ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).comp continuousFourierCLM

/-- On unit-period fields the ambient-circle mean equals the unit-interval integral. -/
theorem periodOneCircleMean_eq_integral (f : C(AddCircle (2:ℝ),ℂ))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2:ℝ))) 1) :
    periodOneCircleMean f = ∫ x in (0:ℝ)..1, f (x : AddCircle (2:ℝ)) := by
  let g := fun x : ℝ => f (x : AddCircle (2:ℝ))
  have hc : Continuous g := f.continuous.comp continuous_quotient_mk'
  change continuousFourierCLM f 0 = _
  rw [continuousFourierCLM_apply,← periodTwoCoefficient_circle]
  change periodTwoCoefficient g 0 = _
  rw [show (0:ℤ) = 2*0 by norm_num,
    periodTwoCoefficient_periodic_even g hp (hc.intervalIntegrable 0 1),
    show periodOneCoefficient g 0 = unitFourierCoefficient g 0 from
      (unitFourierCoefficient_eq_fourierCoeffOn g 0).symm]
  simp only [unitFourierCoefficient,mul_zero,neg_zero,wave_zero,mul_one]
  rfl

end NLS.Fourier
