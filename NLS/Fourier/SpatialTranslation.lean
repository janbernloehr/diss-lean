import NLS.SequenceSpaces.SpatialTranslation
import NLS.Fourier.PeriodOneCoefficients

/-! # Physical meaning of the Fourier translation group

For absolutely summable coefficients the isometric phase rotation is
exactly translation of the synthesized function, with the positive
spatial sign and both Fourier period conventions verified.
-/

noncomputable section
namespace NLS.Fourier

/-- Period-two coefficient translation synthesizes to `f(x+t)`. -/
theorem continuousSynthesis_spatialTranslation (t : ℝ) (a : Coeff 1) (x : ℝ) :
    continuousSynthesis (Coeff.spatialTranslation Real.pi t a) (x : AddCircle (2 : ℝ)) =
      continuousSynthesis a ((x+t : ℝ) : AddCircle (2 : ℝ)) := by
  simp only [continuousSynthesis_apply, Coeff.spatialTranslation_apply, wave_add_argument]
  apply tsum_congr
  intro n
  have he : Complex.exp ((t*(Real.pi*n) : ℝ)*Complex.I) = wave n t := by
    unfold wave
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Period-one coefficient translation has the same physical displacement, without a factor two. -/
theorem periodOneSynthesis_spatialTranslation (t : ℝ) (a : Coeff 1) (x : ℝ) :
    periodOneSynthesis (Coeff.spatialTranslation (2*Real.pi) t a) x =
      periodOneSynthesis a (x+t) := by
  unfold periodOneSynthesis
  rw [Coeff.periodDouble_spatialTranslation, continuousSynthesis_spatialTranslation]

/-- The original Fourier integrals of a translated synthesized source carry its exact phase. -/
theorem periodOneCoefficient_translated_synthesis (t : ℝ) (a : Coeff 1) (n : ℤ) :
    periodOneCoefficient (fun x => periodOneSynthesis a (x+t)) n =
      Complex.exp ((t*((2*Real.pi)*n) : ℝ)*Complex.I)*a n := by
  simp only [← periodOneSynthesis_spatialTranslation, periodOneCoefficient_synthesis,
    Coeff.spatialTranslation_apply]

end NLS.Fourier
