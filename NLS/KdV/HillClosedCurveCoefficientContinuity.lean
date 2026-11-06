import NLS.KdV.HillClosedCurveDirections
import NLS.FunctionalAnalysis.ClosedUnitCurveContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The original continuous Hill Fourier realization is continuous in its physical uniform norm. -/
theorem continuous_hillContinuousCoefficients : Continuous hillContinuousCoefficients :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm.continuous.comp
    Fourier.continuousFourierCLM.continuous

/-- A continuously varying family of actual closed physical unit curves gives a
continuous family of original weighted period-one Hill coefficient sources. -/
theorem continuous_hillClosedCurveCoefficients_family {A : Type} [TopologicalSpace A]
    (f : A → Curve ℂ) (hf : ∀ a, f a ⟨0,by norm_num⟩=f a ⟨1,by norm_num⟩)
    (hF : Continuous f) :
    Continuous (fun a => hillClosedCurveCoefficients (f a) (hf a)) :=
  continuous_hillContinuousCoefficients.comp (continuous_closedUnitCurvePeriodTwo_family f hf hF)

end NLS.KdV
