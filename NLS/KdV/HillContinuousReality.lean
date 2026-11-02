import NLS.KdV.HillRealSpectrum
import NLS.KdV.HillDiscriminantComparison

/-! # Physical real continuous potentials have the actual Fourier reality symmetry -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace NLS.KdV

theorem isRealHillPotential_hillContinuousCoefficients (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0) :
    IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) := by
  intro k
  simp only [SpectralWeight.toCoeff_apply, hillContinuousCoefficients_apply]
  change fourierCoeff Q (-k) = conj (fourierCoeff Q k)
  simp only [fourierCoeff, neg_neg, smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : conj (Q x) = Q x := by apply Complex.ext <;> simp [hQ x]
  simp only [map_mul, hx, ← fourier_neg, neg_neg]

end NLS.KdV
