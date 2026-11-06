import NLS.Articles.KdVKdV2Frequencies.NativePhysicalHamiltonianVariations
import NLS.Fourier.PeriodOneSingleMode

/-! # Fourier samples of the independent physical Hamiltonian covectors

Single smooth unit-period waves test every coefficient, with the frequency
reversal required by complex bilinear duality. The native Hamiltonians here
are defined independently of all spectral actions.
-/
noncomputable section
set_option autoImplicit false
open Complex NLS.KdV NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

/-- Exact Fourier sample of the printed KdV Hamiltonian differential. -/
theorem fderiv_nativeKdVHamiltonian_single (q : ScalarSobolev 1) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hq : ∀ n : ℤ, q.val n=periodOneCoefficient f n) (k : ℤ) :
    (fderiv ℂ nativeKdVHamiltonian q)
      (WeightedCoeff.ofFinsupp (Weight.sobolev ((1 : ℕ) : ℝ)) 2 (Finsupp.single (-k) 1)) =
      periodOneCoefficient (DifferentialPolynomial.evaluate f 0 kdvGradient) k := by
  rw [fderiv_nativeKdVHamiltonian_physical q _ f (wave (2*(-k))) hf
    (contDiff_wave_infty _) hp (periodic_wave_even _) hq (by
      intro n
      rw [WeightedCoeff.ofFinsupp_apply,periodOneCoefficient_wave_even])]
  rw [periodOneCoefficient,←unitFourierCoefficient_eq_fourierCoeffOn]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x _
  simp only [mul_neg]
  ring

/-- Exact Fourier sample of the printed fifth-order Hamiltonian differential. -/
theorem fderiv_nativeKdV2Hamiltonian_single (q : ScalarSobolev 2) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hq : ∀ n : ℤ, q.val n=periodOneCoefficient f n) (k : ℤ) :
    (fderiv ℂ nativeKdV2Hamiltonian q)
      (WeightedCoeff.ofFinsupp (Weight.sobolev ((2 : ℕ) : ℝ)) 2 (Finsupp.single (-k) 1)) =
      periodOneCoefficient (DifferentialPolynomial.evaluate f 0 kdv2Gradient) k := by
  rw [fderiv_nativeKdV2Hamiltonian_physical q _ f (wave (2*(-k))) hf
    (contDiff_wave_infty _) hp (periodic_wave_even _) hq (by
      intro n
      rw [WeightedCoeff.ofFinsupp_apply,periodOneCoefficient_wave_even])]
  rw [periodOneCoefficient,←unitFourierCoefficient_eq_fourierCoeffOn]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x _
  simp only [mul_neg]
  ring

end NLS.Articles.KdVKdV2Frequencies
