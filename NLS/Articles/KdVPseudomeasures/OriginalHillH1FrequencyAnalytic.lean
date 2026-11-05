import NLS.Articles.KdVPseudomeasures.OriginalHillH1FrequencyActionFibers
import NLS.SequenceSpaces.FourierRealContractiveComplexification
import NLS.ComplexAnalysis.RealAnalyticCoordinateDivision

/-! The genuine normalized physical H1 KdV mode frequencies are real
analytic on the ENTIRE actual canonical domain, including every collapsed
mode. Contractive complexification applies to the ORIGINAL physical real
Fourier form; no nonzero-gap or auxiliary real-coordinate assumption remains. -/
noncomputable section
open NLS.WeightedCoeff NLS.ComplexAnalysis
namespace NLS.Articles.KdVPseudomeasures

theorem analyticAt_hillH1KdVFrequency (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    AnalyticAt ℝ (hillH1KdVFrequency n) z := by
  let c := fourierRealContractiveComplexification (p := 2)
    (Weight.signedSobolev (signedStepOrder (1/2) 1)) (Weight.signedSobolev_neg _)
  have hF : AnalyticAt ℝ (fun a => (1/2:ℝ)*hillH1RealModeDerivative n a) z :=
    analyticAt_const.mul (analyticAt_hillH1RealModeDerivative n z)
  apply @analyticAt_of_coordinate_mul
    (RealSignedHilbert (signedStepOrder (1/2) 1))
    (zeroModeSubmodule (Weight.signedSobolev (signedStepOrder (1/2) 1)) 2)
    inferInstance inferInstance inferInstance inferInstance c
    (fun a => (1/2:ℝ)*hillH1RealModeDerivative n a) (hillH1KdVFrequency n)
    (hillH1RealModeCoordinate n) (hillH1ModeCLM n 1) z
    (hillH1RealModeCoordinate_direction n) hF (continuous_hillH1KdVFrequency n)
  intro a
  change hillH1RealModeCoordinate n a*hillH1TransverseSlope n a=(1/2:ℝ)*hillH1RealModeDerivative n a
  rw [hillH1RealModeDerivative_eq_twice_coordinate_slope]
  ring

/-- Analyticity also holds in the original physical H1 potential, using
the SAME actual canonical coordinate map. -/
theorem analyticAt_hillH1KdVFrequency_actual_coordinates (n : ℕ+)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    AnalyticAt ℝ (fun p => hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv p)) q :=
  (analyticAt_hillH1KdVFrequency n _).comp ((hillIntegerSobolevEquiv 1).analytic q)

end NLS.Articles.KdVPseudomeasures
