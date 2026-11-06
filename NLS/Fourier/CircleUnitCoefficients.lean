import NLS.Fourier.PeriodTwoRestrictionL2

/-! # Bounded physical unit-interval coefficients of a circle L² field -/
noncomputable section
open MeasureTheory Set
namespace NLS.Fourier

/-- Restrict an arbitrary circle L² field to (0,1] and take its original
unit-period integral coefficients. No period-one assumption is required. -/
def circleUnitCoefficients : CircleL2 →L[ℂ] Coeff 2 :=
  (periodTwoToUnit (by norm_num) (by simp)).comp
    l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem circleUnitCoefficients_apply (f : CircleL2) (n : ℤ) :
    circleUnitCoefficients f n = periodOneCoefficient (circlePullback f) n := by
  have he : periodTwoL2Coefficients (circlePullback f) (memLp_circlePullback f) =
      l2Synthesis.symm f := by
    ext j
    rw [periodTwoL2Coefficients_apply, periodTwoCoefficient_circlePullback]
    change fourierCoeff f j = fourierBasis.repr f j
    rw [fourierBasis_repr]
  have h := periodTwoToUnit_two_ofFunction (circlePullback f) (memLp_circlePullback f) n
  rw [he] at h
  simpa only [circleUnitCoefficients, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    periodOneCoefficient,
    intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1)] using! h

/-- Almost-everywhere physical agreement identifies the actual coefficients. -/
theorem circleUnitCoefficients_eq_classical (f : CircleL2) (g : ℝ → ℂ)
    (h : circlePullback f =ᵐ[volume.restrict (Ioc 0 1)] g) (n : ℤ) :
    circleUnitCoefficients f n = periodOneCoefficient g n := by
  rw [circleUnitCoefficients_apply, periodOneCoefficient, periodOneCoefficient]
  exact congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1) h) n

end NLS.Fourier
