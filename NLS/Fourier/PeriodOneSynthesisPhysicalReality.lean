import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.Fourier.IntervalBilinearParseval

/-! Literal reality and physical mean for unit-period Fourier series. -/
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate
namespace NLS.Fourier

theorem periodOneCoefficient_zero_eq_integral (f : ℝ → ℂ) :
    periodOneCoefficient f 0 = ∫ x in (0 : ℝ)..1, f x := by
  rw [periodOneCoefficient, ← unitFourierCoefficient_eq_fourierCoeffOn]
  simp only [unitFourierCoefficient, mul_zero, neg_zero, wave_zero, mul_one]

theorem periodOneSynthesis_conj_of_reflection (a : Coeff 1)
    (ha : ∀ k, a (-k) = conj (a k)) (x : ℝ) :
    conj (periodOneSynthesis a x) = periodOneSynthesis a x := by
  have hfix : star (Coeff.reflection a) = a := by
    ext k
    change conj (a (-k)) = a k
    rw [ha, conj_conj]
  rw [← periodOneSynthesis_conjugateReflection, hfix]

end NLS.Fourier
