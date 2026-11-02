import NLS.Fourier.PeriodOneFourierUniqueness
import NLS.Fourier.IntervalBilinearParseval
import NLS.Fourier.DistributionModulation

/-! # Uniqueness from smooth periodic variational tests -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace NLS.Fourier

/-- Fourier waves are smooth periodic tests, so equality of all such physical
pairings determines a continuous periodic gradient pointwise. -/
theorem eq_of_periodic_integral_mul_eq (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (h : ∀ v : ℝ → ℂ, ContDiff ℝ ∞ v → Function.Periodic v 1 →
      (∫ x in (0 : ℝ)..1, v x*f x) = ∫ x in (0 : ℝ)..1, v x*g x) : f = g := by
  apply eq_of_periodOneCoefficient_eq f g hf hg hpf hpg
  intro n
  have hp : Function.Periodic (wave (-(2*n))) 1 := by
    intro x
    rw [wave_add_argument, show -(2*n) = 2*(-n) by ring, wave_even_at_one, mul_one]
  have he := h (wave (-(2*n))) (contDiff_wave_infty _) hp
  have hc (u : ℝ → ℂ) : periodOneCoefficient u n =
      ∫ x in (0 : ℝ)..1, wave (-(2*n)) x*u x := by
    rw [periodOneCoefficient, ← unitFourierCoefficient_eq_fourierCoeffOn]
    unfold unitFourierCoefficient
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  rw [hc f, hc g]
  exact he

end NLS.Fourier
