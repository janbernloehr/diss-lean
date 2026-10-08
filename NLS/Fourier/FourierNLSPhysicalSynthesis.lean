import NLS.Fourier.LocalSmoothFourierNLS

/-! # Continuous physical realization of Fourier NLS trajectories

The actual period-one Fourier series defines a curve in the uniform norm
on the period-two ambient circle, with the original unit-period coefficients.
-/
noncomputable section
open Set
namespace NLS.Fourier

/-- Physical period-one realization as a continuous function on the ambient circle. -/
def fourierNLSPhysicalCurve (w : SpectralWeight) (z : ℝ → WeightedCoeff w.toWeight 1)
    (time : ℝ) : C(AddCircle (2 : ℝ), ℂ) :=
  continuousSynthesis (Coeff.periodDouble (w.toCoeff (z time)))

@[simp] theorem fourierNLSPhysicalCurve_apply (w : SpectralWeight)
    (z : ℝ → WeightedCoeff w.toWeight 1) (time x : ℝ) :
    fourierNLSPhysicalCurve w z time (x : AddCircle (2 : ℝ)) =
      periodOneSynthesis (w.toCoeff (z time)) x := rfl

/-- Fourier-space continuity supplies continuity in the uniform physical norm. -/
theorem IsFourierNLSTrajectoryOn.continuous_physical
    {w : SpectralWeight} {a b : ℝ} {z : ℝ → WeightedCoeff w.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn w a b z) :
    ContinuousOn (fourierNLSPhysicalCurve w z) (Icc a b) := by
  have h := continuousSynthesisCLM.continuous.comp_continuousOn
    ((Coeff.periodDouble (p := 1)).continuous.comp_continuousOn
      (w.toCoeff.continuous.comp_continuousOn hz.continuous))
  simpa only [Function.comp_def,continuousSynthesisCLM_apply,fourierNLSPhysicalCurve] using! h

/-- The physical curve is period one, not merely period two. -/
theorem fourierNLSPhysicalCurve_periodic (w : SpectralWeight)
    (z : ℝ → WeightedCoeff w.toWeight 1) (time : ℝ) :
    Function.Periodic (fun x : ℝ => fourierNLSPhysicalCurve w z time (x : AddCircle (2 : ℝ))) 1 :=
  periodOneSynthesis_periodic _

/-- Actual unit-interval Fourier integrals recover the trajectory's original coefficients. -/
@[simp] theorem periodOneCoefficient_fourierNLSPhysicalCurve (w : SpectralWeight)
    (z : ℝ → WeightedCoeff w.toWeight 1) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => fourierNLSPhysicalCurve w z time (x : AddCircle (2 : ℝ))) n =
      (z time).val n := by
  simp only [fourierNLSPhysicalCurve_apply,periodOneCoefficient_synthesis,SpectralWeight.toCoeff_apply]

end NLS.Fourier
