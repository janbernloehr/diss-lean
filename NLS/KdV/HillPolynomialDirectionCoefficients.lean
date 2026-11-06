import NLS.KdV.HillPolynomialDirections
import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.KdV.HillUnitWeightLift

/-! # Literal Fourier coefficients of physical polynomial directions -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.Fourier NLS.DifferentialPolynomial NLS.LinearVolterra
open scoped ContDiff
namespace NLS.KdV

/-- Original even insertion retains every physical unit-period coefficient. -/
theorem hillPolynomialDirection_even_coefficient (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (P : Polynomial) (k : ℤ) :
    hillPolynomialDirection f hf P (2*k) = periodOneCoefficient (evaluate f 0 P) k := by
  rw [hillPolynomialDirection,Coeff.periodDouble_even,unitCurveCoefficientsCLM_apply,
    unitCurveCoefficients_apply]
  simp only [periodOneCoefficient,←unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  simp only [hillPolynomialCurve,scalarPotentialCurve,NLS.LinearVolterra.extend,projIcc_of_mem _ hx']
  rfl

/-- The actual rough source of a physical polynomial direction has the
original unit-period Fourier sequence, without any sign or scale change. -/
theorem hillOriginalHminusSource_polynomialDirection (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (P : Polynomial) (k : ℤ) :
    (hillOriginalHminusSource (hillUnitWeightLift 2 (hillPolynomialDirection f hf P))).val k =
      periodOneCoefficient (evaluate f 0 P) k := by
  rw [hillOriginalHminusSource_apply]
  rw [hillUnitWeightLift_apply]
  exact hillPolynomialDirection_even_coefficient f hf P k

end NLS.KdV
