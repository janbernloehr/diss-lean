import NLS.FunctionalAnalysis.ClosedUnitCurveLinearRealization
import NLS.KdV.HillClosedCurveDirections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- A bounded complex-linear extension of the original physical closed-curve coefficient realization. -/
def hillCurveRealizationCLM : Curve ℂ →L[ℂ] WeightedCoeff SpectralWeight.one.toWeight 2 :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Fourier.continuousFourierCLM.comp (closedUnitCurvePeriodTwoCLM.comp closedUnitCurveProjectionCLM))

/-- On every actual closed curve the bounded extension is exactly the original Hill source. -/
theorem hillCurveRealizationCLM_closed (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    hillCurveRealizationCLM f=hillClosedCurveCoefficients f hf := by
  change (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm
      (Fourier.continuousFourierCLM (closedUnitCurvePeriodTwo (closedUnitCurveProjectionCLM f).val _))=
    (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm
      (Fourier.continuousFourierCLM (closedUnitCurvePeriodTwo f hf))
  simp only [closedUnitCurveProjectionCLM_fixed f hf]

end NLS.KdV
