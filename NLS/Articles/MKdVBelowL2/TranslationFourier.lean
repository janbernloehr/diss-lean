import NLS.Fourier.SpatialTranslation

/-! # Period-one physical renormalization multiplier

Fourier convention: coefficient n integrates against exp(-2πinx).
These statements concern actual synthesized functions with summable
coefficients, not an assumed interpretation of Birkhoff coordinates.
-/
noncomputable section
namespace NLS.Articles.MKdVBelowL2

/-- The physical renormalizing translation has phase `-12 π n M t`. -/
theorem coefficient_renormalizing_translation (M t : ℝ) (a : Coeff 1) (n : ℤ) :
    Fourier.periodOneCoefficient
      (fun x => Fourier.periodOneSynthesis a (x - 6 * M * t)) n =
      Complex.exp (((-12 * Real.pi * (n : ℝ) * M * t : ℝ) : ℂ) * Complex.I) * a n := by
  have h := Fourier.periodOneCoefficient_translated_synthesis (-6 * M * t) a n
  have hx (x : ℝ) : x - 6 * M * t = x + -6 * M * t := by ring
  have he : (-6 * M * t) * ((2 * Real.pi) * (n : ℝ)) =
      -12 * Real.pi * (n : ℝ) * M * t := by ring
  simpa only [hx, he] using h

/-- The inverse physical translation restores phase `12 π n M t`. -/
theorem coefficient_original_translation (M t : ℝ) (a : Coeff 1) (n : ℤ) :
    Fourier.periodOneCoefficient
      (fun x => Fourier.periodOneSynthesis a (x + 6 * M * t)) n =
      Complex.exp (((12 * Real.pi * (n : ℝ) * M * t : ℝ) : ℂ) * Complex.I) * a n := by
  have h := Fourier.periodOneCoefficient_translated_synthesis (6 * M * t) a n
  have he : (6 * M * t) * ((2 * Real.pi) * (n : ℝ)) =
      12 * Real.pi * (n : ℝ) * M * t := by ring
  simpa only [he] using h

end NLS.Articles.MKdVBelowL2
