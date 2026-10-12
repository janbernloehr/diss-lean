import NLS.Fourier.SmoothPeriodicTestLift
import NLS.Fourier.SobolevDistributionPairing

/-! # Corrected scalar duality on every original smooth periodic test

The Schwartz lift recovers every smooth test and its actual normalized Fourier
coefficients. Thus the corrected pairing agrees with genuine distributional
action throughout the real Sobolev scale, including conjugate endpoints.
-/
noncomputable section
open scoped ENNReal SchwartzMap ContDiff
namespace NLS.Fourier
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Every smooth periodic test has coefficients in every Sobolev class and Banach exponent. -/
theorem smoothPeriodicTestLift_sobolev_coefficients (s : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 2) (n : ℤ) :
    (periodizationSobolevCoefficients (q := q) s (smoothPeriodicTestLift f)).val n =
      periodTwoCoefficient f n := by
  rw [periodizationSobolevCoefficients_val,← periodTwoCoefficient_circle]
  congr 1
  funext x
  exact periodization_smoothPeriodicTestLift f hf hp x

variable [p.HolderConjugate q]

/-- The corrected scalar pairing agrees with actual normalized distributional action
on every smooth period-two test, without an extra decay or growth hypothesis. -/
theorem sobolevBilinearPairing_smooth_periodic (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 2)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) (hb : ∀ n, b.val n = periodTwoCoefficient f n) :
    WeightedCoeff.sobolevBilinearPairing s a b =
      sobolevDistributionSynthesisCLM s a (SchwartzMap.smulLeftCLM ℂ f (coefficientTest 0)) := by
  have he : b = periodizationSobolevCoefficients (-s) (smoothPeriodicTestLift f) := by
    apply Subtype.ext
    funext n
    rw [hb,smoothPeriodicTestLift_sobolev_coefficients (-s) f hf hp]
  rw [he,sobolevBilinearPairing_periodization,smoothPeriodicTestLift,map_smul]
  simp only [smul_eq_mul]
  ring

/-- The same formula for any actual periodic distribution with these Fourier coefficients. -/
theorem periodicDistribution_sobolevBilinearPairing_smooth (s : ℝ)
    (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (a : WeightedCoeff (Weight.sobolev s) p) (ha : ∀ n, a.val n = T (coefficientTest n))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 2)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) (hb : ∀ n, b.val n = periodTwoCoefficient f n) :
    WeightedCoeff.sobolevBilinearPairing s a b =
      T (SchwartzMap.smulLeftCLM ℂ f (coefficientTest 0)) := by
  rw [sobolevBilinearPairing_smooth_periodic s a f hf hp b hb]
  exact congrArg (fun U : 𝓢'(ℝ, ℂ) => U (SchwartzMap.smulLeftCLM ℂ f (coefficientTest 0)))
    (weightedDistributionSynthesis_eq_of_periodic_coefficients _ _ hT a ha)

end NLS.Fourier
