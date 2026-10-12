import NLS.SequenceSpaces.SobolevSesquilinearPairing
import NLS.Fourier.ArbitraryPeriodDistributionPairing
import NLS.Fourier.ArbitraryPeriodBilinearParseval

/-! # Physical meaning of the Sobolev sesquilinear product

At every positive period, pairing an actual periodic distribution against
a smooth conjugated test gives the same-index sesquilinear coefficient
formula. The normalized Schwartz window retains the original factor 1/L.
The L2 integral identity is included separately for two function inputs.
-/
noncomputable section
open scoped ENNReal SchwartzMap ContDiff
open MeasureTheory Set
namespace NLS.Fourier

/-- Actual Fourier coefficients of the conjugated smooth test, at arbitrary Sobolev order. -/
theorem sobolevConjugation_smooth_coefficients {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (L s : ℝ) (f : ℝ → ℂ) (b : WeightedCoeff (Weight.sobolev s) q)
    (hb : ∀ n, b.val n = intervalFourierCoefficient L f n) (n : ℤ) :
    (WeightedCoeff.sobolevConjugation s b).val n =
      intervalFourierCoefficient L (fun x => star (f x)) n := by
  simp only [WeightedCoeff.sobolevConjugation_apply,hb,Complex.star_def]
  exact (intervalFourierCoefficient_conj f n).symm

/-- The sesquilinear product is normalized distributional action on the conjugated test. -/
theorem periodicDistribution_sobolevSesquilinearPairing {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (L : ℝ) (hL : 0 < L) (s : ℝ) (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodicDistribution L T)
    (a : WeightedCoeff (Weight.sobolev s) p) (ha : ∀ n, a.val n = T (periodCoefficientTest L hL n))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) (hb : ∀ n, b.val n = intervalFourierCoefficient L f n) :
    WeightedCoeff.sobolevSesquilinearPairing s a b =
      T (SchwartzMap.smulLeftCLM ℂ (fun x => star (f x)) (periodCoefficientTest L hL 0)) := by
  apply periodicDistribution_sobolevBilinearPairing_arbitraryPeriod L hL s T hT a ha
    (fun x => star (f x)) (Complex.conjCLE.contDiff.comp hf) (fun x => congrArg star (hp x))
    (WeightedCoeff.sobolevConjugation (-s) b)
  exact sobolevConjugation_smooth_coefficients L (-s) f b hb

/-- Every smooth periodic test supplies its unique coefficient representative automatically. -/
theorem existsUnique_sesquilinear_smooth_test {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (L : ℝ) (hL : 0 < L) (s : ℝ) (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodicDistribution L T)
    (a : WeightedCoeff (Weight.sobolev s) p) (ha : ∀ n, a.val n = T (periodCoefficientTest L hL n))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L) :
    ∃! b : WeightedCoeff (Weight.sobolev (-s)) q,
      (∀ n, b.val n = intervalFourierCoefficient L f n) ∧
      WeightedCoeff.sobolevSesquilinearPairing s a b =
        T (SchwartzMap.smulLeftCLM ℂ (fun x => star (f x)) (periodCoefficientTest L hL 0)) := by
  obtain ⟨b,hb,hu⟩ := existsUnique_smooth_arbitraryPeriod_coefficients (q := q) L hL (-s) f hf hp
  exact ⟨b,⟨hb,periodicDistribution_sobolevSesquilinearPairing L hL s T hT a ha f hf hp b hb⟩,
    fun c hc => hu c hc.1⟩

/-- Agreement with the original normalized physical L2 inner product at every positive period. -/
theorem sobolevSesquilinearPairing_eq_intervalIntegral {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (L : ℝ) (hL : 0 < L) (s : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (hg : MemLp g 2 (volume.restrict (Ioc 0 L)))
    (a : WeightedCoeff (Weight.sobolev s) p) (ha : ∀ n, a.val n = intervalFourierCoefficient L f n)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) (hb : ∀ n, b.val n = intervalFourierCoefficient L g n) :
    WeightedCoeff.sobolevSesquilinearPairing s a b =
      (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*star (g x) := by
  rw [WeightedCoeff.sobolevSesquilinearPairing_apply]
  simp only [ha,hb,Complex.star_def]
  exact (hasSum_sesquilinear_intervalFourierCoefficient hL hf hg).tsum_eq

end NLS.Fourier
