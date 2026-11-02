import NLS.Fourier.PeriodicDistributionIdentification
import NLS.Fourier.DistributionPeriodicity
import NLS.Fourier.SmoothPeriodicDistribution

/-! # Period-one distributions among arbitrary period-two distributions

No finite-exponent or measure hypothesis is imposed. Reconstruction of
arbitrary periodic tempered distributions identifies physical period one
with the vanishing of the odd normalized Fourier coefficients.
-/
noncomputable section
open scoped SchwartzMap FourierTransform
namespace NLS.Fourier

/-- Translation of a coefficient test detects the physical Fourier phase. -/
theorem IsPeriodTwoDistribution.translate_coefficientTest {T : 𝓢'(ℝ,ℂ)}
    (hT : IsPeriodTwoDistribution T) (t : ℝ) (n : ℤ) :
    T (SchwartzMap.compSubConstCLM ℂ t (coefficientTest n)) =
      T (coefficientTest n) * wave n t := by
  rw [hT.fourier_reconstruction]
  simp only [fourier_sample_translate, coefficientTest,
    FourierTransform.fourier_fourierInv_eq, frequencyTest_sample]
  simp

/-- The source's physical period-one condition, at arbitrary distribution order. -/
theorem IsPeriodTwoDistribution.period_one_iff_odd {T : 𝓢'(ℝ,ℂ)}
    (hT : IsPeriodTwoDistribution T) :
    IsPeriodicDistribution 1 T ↔ ∀ k : ℤ, T (coefficientTest (2*k+1)) = 0 := by
  constructor
  · intro h k
    have ht := h (coefficientTest (2*k+1))
    rw [hT.translate_coefficientTest, wave_odd_at_one] at ht
    linear_combination -(1/2:ℂ) * ht
  · intro h g
    rw [hT.fourier_reconstruction, hT.fourier_reconstruction]
    apply tsum_congr
    intro n
    rw [fourier_sample_translate, ← mul_assoc]
    by_cases hn : n % 2 = 0
    · have he : n = 2*(n/2) := by omega
      rw [he, wave_even_at_one, mul_one]
    · have he : n = 2*(n/2)+1 := by omega
      rw [he, h, zero_mul, zero_mul]

namespace SmoothPeriodicTest.Distribution

/-- Period two native Fourier coefficients are the existing tempered samples. -/
theorem toTempered_coefficient_two (u : SmoothPeriodicTest.Distribution (2:ℝ)) (n : ℤ) :
    u.toTempered (coefficientTest n) = u (SmoothPeriodicTest.mode (-n)) := by
  simpa only [periodCoefficientTest_two] using u.toTempered_coefficient n

/-- Exact odd-mode characterization on the original smooth-test distributions. -/
theorem toTempered_period_one_iff_odd (u : SmoothPeriodicTest.Distribution (2:ℝ)) :
    IsPeriodicDistribution 1 u.toTempered ↔
      ∀ k : ℤ, u (SmoothPeriodicTest.mode (-(2*k+1))) = 0 := by
  have hT : IsPeriodTwoDistribution u.toTempered := u.toTempered_periodic
  simpa only [toTempered_coefficient_two] using hT.period_one_iff_odd

end SmoothPeriodicTest.Distribution
end NLS.Fourier
