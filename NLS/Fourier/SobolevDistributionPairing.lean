import NLS.SequenceSpaces.SobolevBilinearPairing
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.Fourier.WeightedDistributionIdentification

/-! # Sobolev bilinear pairing agrees with actual distributional action

Every Schwartz periodization has coefficients in every real Sobolev class
and every Banach exponent. Pairing against these coefficients gives one half
the real-line distributional action, exactly the normalized period-two action.
-/
noncomputable section
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Actual periodized Schwartz coefficients at arbitrary real Sobolev regularity. -/
def periodizationSobolevCoefficients (s : ℝ) (g : 𝓢(ℝ, ℂ)) :
    WeightedCoeff (Weight.sobolev s) q :=
  (WeightedCoeff.weightEquiv (Weight.sobolev s) q).symm
    ((1/2 : ℂ) • Coeff.reflection
      (Coeff.exponentInclusion (show 1 ≤ q from Fact.out)
        (weightedSchwartzSamples (Weight.sobolev (-s)) (Weight.hasTemperedInverse_sobolev (-s)) (𝓕 g))))

/-- These are the physical normalized Fourier coefficients, not abstract test values. -/
theorem periodizationSobolevCoefficients_val (s : ℝ) (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    (periodizationSobolevCoefficients (q := q) s g).val n = fourierCoeff (periodizationCLM g) n := by
  rw [fourierCoeff_periodization]
  change ((1/2 : ℂ)*((𝓕 g) (-((-n : ℤ) : ℝ)/2)/(Weight.sobolev (-s) (-n) : ℂ))) /
    (Weight.sobolev s n : ℂ) = _
  rw [Weight.sobolev_neg]
  simp only [Int.cast_neg,neg_neg]
  have hw : (Weight.sobolev (-s) n : ℂ) = (Weight.sobolev s n : ℂ)⁻¹ := by
    simp [Weight.sobolev_apply,Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+|(n : ℝ)|)]
  rw [hw]
  field_simp [Weight.complex_ne_zero (Weight.sobolev s) n]
  exact mul_div_cancel_right₀ _ (Weight.complex_ne_zero (Weight.sobolev s) n)

variable [p.HolderConjugate q]

/-- The corrected coefficient pairing is the normalized action on every Schwartz periodization. -/
theorem sobolevBilinearPairing_periodization (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (g : 𝓢(ℝ, ℂ)) :
    WeightedCoeff.sobolevBilinearPairing s a (periodizationSobolevCoefficients (q := q) (-s) g) =
      (1/2 : ℂ)*sobolevDistributionSynthesisCLM s a g := by
  rw [WeightedCoeff.sobolevBilinearPairing_apply,sobolevDistributionSynthesisCLM_apply,← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [periodizationSobolevCoefficients_val,fourierCoeff_periodization]
  simp only [Int.cast_neg]
  ring

/-- This identification concerns arbitrary periodic distributions with the stated coefficient regularity. -/
theorem periodicDistribution_sobolevBilinearPairing (s : ℝ) (T : 𝓢'(ℝ, ℂ))
    (hT : IsPeriodTwoDistribution T)
    (a : WeightedCoeff (Weight.sobolev s) p) (ha : ∀ n, a.val n = T (coefficientTest n))
    (g : 𝓢(ℝ, ℂ)) :
    WeightedCoeff.sobolevBilinearPairing s a (periodizationSobolevCoefficients (q := q) (-s) g) =
      (1/2 : ℂ)*T g := by
  rw [sobolevBilinearPairing_periodization]
  congr 1
  exact congrArg (fun U : 𝓢'(ℝ, ℂ) => U g)
    (weightedDistributionSynthesis_eq_of_periodic_coefficients _ _ hT a ha)

end NLS.Fourier
