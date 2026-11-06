import NLS.KdV.HillClosedCurveDirections
import NLS.KdV.HillHminusOriginalSheets
import NLS.Fourier.ACPeriodicUnitCoefficients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.KdV

/-- Every original even coefficient of a closed physical unit curve is
its literal unit-period Fourier integral, at EVERY signed frequency. -/
theorem hillClosedCurveCoefficients_even_apply (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩ = f ⟨1,by norm_num⟩) (k : ℤ) :
    (hillClosedCurveCoefficients f hf).val (2*k) =
      Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend f) k := by
  let Q := closedUnitCurvePeriodTwo f hf
  change (hillContinuousCoefficients Q).val (2*k) = _
  rw [hillContinuousCoefficients_apply,←Fourier.periodTwoCoefficient_circle]
  have he := Fourier.periodTwoCoefficient_periodic_even
    (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) (periodic_closedUnitCurvePeriodTwo f hf)
    ((Q.continuous.comp (by fun_prop)).intervalIntegrable 0 1) k
  rw [he,Fourier.periodOneCoefficient,←Fourier.unitFourierCoefficient_eq_fourierCoeffOn]
  apply Fourier.unitFourierCoefficient_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact closedUnitCurvePeriodic_eq f hf x hx

/-- The original H-minus-one source adapter preserves the exact physical
unit coefficients of every closed curve, including the zero mode. -/
theorem hillOriginalHminusSource_closedCurve_apply (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩ = f ⟨1,by norm_num⟩) (k : ℤ) :
    (hillOriginalHminusSource (hillClosedCurveCoefficients f hf)).val k =
      Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend f) k := by
  rw [hillOriginalHminusSource_apply,hillClosedCurveCoefficients_even_apply]

end NLS.KdV
