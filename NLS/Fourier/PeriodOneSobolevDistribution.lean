import NLS.Fourier.ArbitraryPeriodDistribution
import NLS.Fourier.SobolevDistributionDerivative
import NLS.Fourier.SmoothPeriodicDistributionDerivative

/-! # Physical period-one distributions at every real Sobolev order -/
noncomputable section
open scoped SchwartzMap FourierTransform
namespace NLS.Fourier

def periodOneSobolevDistribution (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] 𝓢'(ℝ,ℂ) :=
  arbitraryPeriodDistributionSynthesisCLM 1 (by norm_num) (Weight.sobolev s)
    (Weight.hasTemperedInverse_sobolev s)

theorem periodOneSobolevDistribution_periodic (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    IsPeriodicDistribution 1 (periodOneSobolevDistribution s a) :=
  arbitraryPeriodDistributionSynthesis_periodic 1 (by norm_num) _ _ a

@[simp] theorem periodOneSobolevDistribution_coefficient (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    periodOneSobolevDistribution s a (periodCoefficientTest 1 (by norm_num) n) = a.val n :=
  arbitraryPeriodDistributionSynthesis_coefficient 1 (by norm_num) _ _ a n

private theorem periodOneSobolevDistribution_eq_dilation (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    periodOneSobolevDistribution s a =
      distributionDilation 2 (by norm_num) (sobolevDistributionSynthesisCLM s a) := by
  change distributionDilation ((1/2 : ℝ)⁻¹) (by norm_num)
    (sobolevDistributionSynthesisCLM s a) = _
  norm_num

/-- The genuine distribution derivative has the exact physical period-one
symbol 2*pi*i*n, across arbitrary positive or negative regularities. -/
theorem periodOneSobolevDistribution_derivative_eq (s t : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) 2) (b : WeightedCoeff (Weight.sobolev t) 2)
    (h : ∀ n : ℤ, b.val n = 2*Complex.I*(Real.pi : ℂ)*n*a.val n) :
    TemperedDistribution.derivCLM ℂ (periodOneSobolevDistribution s a) =
      periodOneSobolevDistribution t b := by
  have he : (2 : ℂ) • TemperedDistribution.derivCLM ℂ (sobolevDistributionSynthesisCLM s a) =
      sobolevDistributionSynthesisCLM t b := by
    ext g
    rw [_root_.smul_apply, smul_eq_mul, sobolevDistributionDerivative_apply,
      ← tsum_mul_left, sobolevDistributionSynthesisCLM_apply]
    apply tsum_congr
    intro n
    rw [h n]
    ring
  rw [periodOneSobolevDistribution_eq_dilation, periodOneSobolevDistribution_eq_dilation,
    distributionDilation_deriv]
  norm_num only [Complex.ofReal_ofNat]
  change (2 : ℂ) • (distributionDilationCLM 2 (by norm_num)) _ =
    (distributionDilationCLM 2 (by norm_num)) _
  rw [← map_smul, he]

end NLS.Fourier
