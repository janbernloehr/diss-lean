import NLS.Fourier.SmoothInitialFourierNLS
import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.Fourier.IntervalBilinearParseval

/-! # Derivatives and products of smooth unit-period Fourier coefficients

These identities concern actual physical Fourier integrals, at all integer
frequencies, with the `2π` derivative convention.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace NLS.Fourier

private theorem coefficient_eq_unit (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient f n = unitFourierCoefficient f n :=
  (unitFourierCoefficient_eq_fourierCoeffOn f n).symm

@[simp] theorem periodOneCoefficient_neg (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient (-f) n = -periodOneCoefficient f n := by
  simp only [coefficient_eq_unit,unitFourierCoefficient,Pi.neg_apply,neg_mul,
    intervalIntegral.integral_neg]

theorem periodOneCoefficient_add (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    periodOneCoefficient (f+g) n = periodOneCoefficient f n+periodOneCoefficient g n := by
  simp only [coefficient_eq_unit,unitFourierCoefficient,Pi.add_apply,add_mul]
  exact intervalIntegral.integral_add
    ((hf.mul (continuous_wave _)).intervalIntegrable 0 1)
    ((hg.mul (continuous_wave _)).intervalIntegrable 0 1)

theorem periodOneCoefficient_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, Continuous (f i)) (n : ℤ) :
    periodOneCoefficient (∑ i ∈ S, f i) n = ∑ i ∈ S, periodOneCoefficient (f i) n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coefficient_eq_unit,unitFourierCoefficient]
  | @insert a S ha ih =>
    have hS : Continuous (∑ i ∈ S, f i) := by
      change Continuous (fun x => (∑ i ∈ S, f i) x)
      simp only [Finset.sum_apply]
      exact continuous_finsetSum _ (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha,Finset.sum_insert ha,
      periodOneCoefficient_add (f a) (∑ i ∈ S, f i) (hf a (Finset.mem_insert_self _ _)) hS,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Smooth periodic differentiation has its exact unit-period multiplier,
including the zero and negative frequencies. -/
theorem periodOneCoefficient_deriv_of_smooth_periodic (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (n : ℤ) :
    periodOneCoefficient (deriv f) n = 2*Complex.I*(Real.pi:ℂ)*n*periodOneCoefficient f n := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hpd := ZakharovShabat.periodic_deriv_of_periodic f 1 hp
  have hp2 : Function.Periodic f 2 := by simpa using! hp.nat_mul 2
  rw [← periodTwoCoefficient_periodic_even (deriv f) hpd (hd.continuous.intervalIntegrable 0 1),
    periodTwoCoefficient_deriv_of_ac_periodic
      ((hf.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval)
      (hd.continuous.intervalIntegrable 0 2) (by simpa only [zero_add] using hp2 0),
    periodTwoCoefficient_periodic_even f hp (hf.continuous.intervalIntegrable 0 1)]
  push_cast
  ring

/-- Smooth periodic multiplication gives the actual infinite coefficient convolution. -/
theorem periodOneCoefficient_mul_of_smooth_periodic (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1) (n : ℤ) :
    periodOneCoefficient (f*g) n =
      ∑' j : ℤ, periodOneCoefficient f (n-j)*periodOneCoefficient g j := by
  let a := SpectralWeight.one.toCoeff (smoothPeriodOneFourierData f hf hpf)
  let b := SpectralWeight.one.toCoeff (smoothPeriodOneFourierData g hg hpg)
  have he : periodOneSynthesis (Coeff.convolution a b) = f*g := by
    funext x
    rw [periodOneSynthesis_convolution,periodOneSynthesis_smoothPeriodOneFourierData,
      periodOneSynthesis_smoothPeriodOneFourierData]
    rfl
  rw [← he,periodOneCoefficient_synthesis,Coeff.convolution_apply]
  simp only [a,b,SpectralWeight.toCoeff_apply,smoothPeriodOneFourierData_apply]

end NLS.Fourier
