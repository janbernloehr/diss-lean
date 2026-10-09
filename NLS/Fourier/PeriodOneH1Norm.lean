import NLS.Fourier.IntervalH1NormIdentification
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian

/-! # Exact physical H1 norms for period-one Fourier data

Parseval uses the physical unit interval, so no factor from the ambient
period-two circle enters. Differentiation retains its multiplier 2*pi*i*n.
-/
noncomputable section
open Set MeasureTheory
namespace NLS.Fourier
open NLS.ZakharovShabat NLS.ComplexAnalysis

/-- Parseval for arbitrary square-integrable unit-interval functions. -/
theorem hasSum_sq_periodOneCoefficient {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    HasSum (fun n => ‖periodOneCoefficient f n‖^2) (∫ s in (0 : ℝ)..1, ‖f s‖^2) := by
  simpa only [periodOneCoefficient,sub_zero,inv_one,one_smul] using
    hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hf

private theorem hasSum_coeff_sq (a : Coeff 2) : HasSum (fun n => ‖a n‖^2) (‖a‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) a

/-- Unit-period synthesis has exactly the original coefficient L2 norm. -/
theorem integral_sq_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    (∫ s in (0 : ℝ)..1, ‖periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))‖^2) =
      ‖scalarInclusion a‖^2 := by
  have h := hasSum_sq_periodOneCoefficient
    (memLp_two_interval (continuous_periodOneSobolevSynthesis a) 0 1 (by norm_num))
  simp only [periodOneCoefficient_periodOneSobolevSynthesis] at h
  exact h.unique (by simpa only [scalarInclusion_apply] using hasSum_coeff_sq (scalarInclusion a))

/-- Parseval for the actual derivative, with the physical multiplier 2*pi*i*n. -/
theorem integral_sq_deriv_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    (∫ s in (0 : ℝ)..1, ‖deriv (fun r : ℝ =>
      periodOneSobolevSynthesis a (r : AddCircle (2 : ℝ))) s‖^2) = ‖periodOneDerivative a‖^2 := by
  have h := hasSum_sq_periodOneCoefficient (memLp_deriv_periodOneSobolevSynthesis a)
  simp only [periodOneCoefficient_deriv_periodOneSobolevSynthesis] at h
  exact h.unique (by simpa only [periodOneDerivative_apply] using hasSum_coeff_sq (periodOneDerivative a))

/-- The integral H1 norm squared is exactly the coefficient graph energy. -/
theorem intervalH1Norm_sq_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    intervalH1Norm (fun s : ℝ => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))) 1 ^ 2 =
      ‖scalarInclusion a‖^2+‖periodOneDerivative a‖^2 := by
  rw [intervalH1Norm_eq_sqrt_energy _ 1 (by norm_num)
    (memLp_two_interval (continuous_periodOneSobolevSynthesis a) 0 1 (by norm_num))
    (memLp_deriv_periodOneSobolevSynthesis a),
    Real.sq_sqrt (intervalH1Energy_nonneg _ (by norm_num : (0 : ℝ) ≤ 1)),
    intervalH1Energy,integral_sq_periodOneSobolevSynthesis,integral_sq_deriv_periodOneSobolevSynthesis]

end NLS.Fourier
