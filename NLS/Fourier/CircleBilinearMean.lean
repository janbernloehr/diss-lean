import NLS.Fourier.CircleUnitCoefficients
import NLS.Fourier.IntervalBilinearParseval
import NLS.SequenceSpaces.ConjugateDuality

/-! # The bounded physical unit-interval mean of two circle L² fields -/
noncomputable section
open MeasureTheory Set
namespace NLS.Fourier

def circleBilinearMean : CircleL2 →L[ℂ] CircleL2 →L[ℂ] ℂ :=
  ((ContinuousLinearMap.compL ℂ CircleL2 (Coeff 2) ℂ).flip circleUnitCoefficients).comp
    (Coeff.dualPairing.comp
      (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp circleUnitCoefficients))

theorem circleBilinearMean_eq_classical (a b : CircleL2) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (ha : circlePullback a =ᵐ[volume.restrict (Ioc 0 1)] f)
    (hb : circlePullback b =ᵐ[volume.restrict (Ioc 0 1)] g) :
    circleBilinearMean a b = ∫ x in (0 : ℝ)..1, f x*g x := by
  change Coeff.dualPairing (Coeff.reflection (circleUnitCoefficients a)) (circleUnitCoefficients b) = _
  rw [Coeff.dualPairing_apply]
  simp_rw [Coeff.reflection_apply, circleUnitCoefficients_eq_classical a f ha,
    circleUnitCoefficients_eq_classical b g hb]
  have he := tsum_bilinear_unitFourierCoefficient hf hg
  simpa only [unitFourierCoefficient_eq_fourierCoeffOn, periodOneCoefficient] using he

end NLS.Fourier
