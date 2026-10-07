import NLS.SequenceSpaces.SobolevPeriodDoubling
import NLS.Fourier.PeriodOneCoefficients
import NLS.Fourier.SobolevDerivative
import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # The physical period-one H¹ representative

Even insertion transports the existing Sobolev fundamental theorem of calculus
without changing the original period-one coefficients. The resulting classical
derivative is square integrable and has multiplier `2πin`, including at negative
frequencies. These facts supply the physical derivative needed for the H¹ NLS energy.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.Fourier
open ZakharovShabat

/-- Bounded synthesis of period-one H¹ coefficients on the ambient period-two circle. -/
def periodOneSobolevSynthesis : ScalarDomain 2 →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  continuousSynthesisCLM.comp
    (Coeff.periodDouble.toContinuousLinearMap.comp (WeightedCoeff.sobolevToL1CLM 2 (by simp)))

@[simp] theorem periodOneSobolevSynthesis_apply (a : ScalarDomain 2) (x : ℝ) :
    periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) =
      periodOneSynthesis (WeightedCoeff.sobolevToL1CLM 2 (by simp) a) x := rfl

/-- The doubled weighted representative is exactly the original unit-period Fourier series. -/
theorem periodOneSobolevSynthesis_eq (a : ScalarDomain 2) :
    periodOneSobolevSynthesis a = sobolevSynthesis (by simp) (Coeff.periodDoubleSobolev a) := by
  apply eq_sobolevSynthesis_of_fourierCoeff
  intro n
  change fourierCoeff (continuousSynthesis
    (Coeff.periodDouble (WeightedCoeff.sobolevToL1CLM 2 (by simp) a))) n = _
  rw [fourierCoeff_continuousSynthesis, Coeff.periodDoubleSobolev_apply]
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    rw [he, Coeff.periodDouble_even, Coeff.periodDouble_even]
    simp
  · have he : n = 2 * (n / 2) + 1 := by omega
    rw [he, Coeff.periodDouble_odd, Coeff.periodDouble_odd]

theorem periodOneSobolevSynthesis_periodic (a : ScalarDomain 2) :
    Function.Periodic (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) 1 :=
  periodOneSynthesis_periodic _

theorem continuous_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    Continuous (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) :=
  continuous_periodOneSynthesis _

@[simp] theorem periodOneCoefficient_periodOneSobolevSynthesis (a : ScalarDomain 2) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) n =
      a.val n := by
  simp only [periodOneSobolevSynthesis_apply, periodOneCoefficient_synthesis,
    WeightedCoeff.sobolevToL1CLM_apply]

/-- Absolute continuity on the actual physical unit interval. -/
theorem absolutelyContinuous_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    AbsolutelyContinuousOnInterval
      (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) 0 1 := by
  rw [periodOneSobolevSynthesis_eq]
  exact (absolutelyContinuous_sobolevSynthesis _).mono
    (show uIcc (0 : ℝ) 1 ⊆ uIcc 0 2 by
      simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
      exact Icc_subset_Icc le_rfl (by norm_num))

/-- The total classical derivative is square integrable on the physical unit interval. -/
theorem memLp_deriv_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    MemLp (deriv (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
      2 (volume.restrict (Ioc 0 1)) := by
  rw [periodOneSobolevSynthesis_eq]
  exact (memLp_deriv_sobolevSynthesis _).mono_measure
    (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (by norm_num)))

theorem intervalIntegrable_deriv_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    IntervalIntegrable (deriv (fun x : ℝ => periodOneSobolevSynthesis a
      (x : AddCircle (2 : ℝ)))) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    ((memLp_deriv_periodOneSobolevSynthesis a).integrable (by norm_num))

/-- Classical differentiation has the period-one Fourier symbol, with no factor two lost. -/
@[simp] theorem periodOneCoefficient_deriv_periodOneSobolevSynthesis
    (a : ScalarDomain 2) (n : ℤ) :
    periodOneCoefficient (deriv (fun x : ℝ => periodOneSobolevSynthesis a
      (x : AddCircle (2 : ℝ)))) n = 2 * Complex.I * (Real.pi : ℂ) * n * a.val n := by
  rw [← periodTwoCoefficient_periodic_even _
    (periodic_deriv_of_periodic _ 1 (periodOneSobolevSynthesis_periodic a))
    (intervalIntegrable_deriv_periodOneSobolevSynthesis a), periodOneSobolevSynthesis_eq,
    periodTwoCoefficient_deriv_sobolevSynthesis, Coeff.periodDoubleSobolev_apply,
    Coeff.periodDouble_even, scalarInclusion_apply]
  push_cast
  ring

/-- Normalization on every signed Fourier mode. -/
@[simp] theorem periodOneSobolevSynthesis_scalarMode (n : ℤ) (c : ℂ) (x : ℝ) :
    periodOneSobolevSynthesis (scalarMode n c) (x : AddCircle (2 : ℝ)) = c * wave (2*n) x := by
  rw [periodOneSobolevSynthesis_eq, Coeff.periodDoubleSobolev_scalarMode, sobolevSynthesis_scalarMode]

end NLS.Fourier
