import NLS.Fourier.ContinuousConjugation
import NLS.KdV.HillRealSpectrum
import NLS.KdV.HillDiscriminantComparison

/-! # Physical reality and conjugate Fourier symmetry for continuous potentials -/

noncomputable section
open MeasureTheory Complex NLS.Fourier
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

theorem hillContinuousPotential_real_of_coefficients
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))) :
    ∀ x : AddCircle (2 : ℝ), (Q x).im = 0 := by
  have hs : star Q = Q := by
    apply continuousFourierCLM_injective
    rw [continuousFourierCLM_star]
    ext k
    simp only [lp.star_apply, Coeff.reflection_apply, continuousFourierCLM_apply]
    have h := hr (-k)
    simp only [neg_neg, SpectralWeight.toCoeff_apply, hillContinuousCoefficients_apply] at h
    exact h.symm
  intro x
  have hc : conj (Q x) = Q x := congrArg (fun F : C(AddCircle (2 : ℝ), ℂ) => F x) hs
  have hi := congrArg Complex.im hc
  simp only [conj_im] at hi
  linarith


end NLS.KdV
