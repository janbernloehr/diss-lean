import NLS.Fourier.WeightedDistributionSynthesis

/-!
# Intrinsic weighted Fourier regularity of periodic distributions

A periodic tempered distribution belongs to a weighted Banach Fourier class
exactly when the weighted coefficient-test sequence is in `lp`. This covers
every real Sobolev exponent, including negative and fractional exponents.
-/

noncomputable section
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted coefficient data with the prescribed values reconstruct any periodic distribution. -/
theorem weightedDistributionSynthesis_eq_of_periodic_coefficients
    (w : Weight) (hw : w.HasTemperedInverse) {T : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) (a : WeightedCoeff w p)
    (ha : ∀ n : ℤ, a.val n = T (coefficientTest n)) : weightedDistributionSynthesis w hw a = T := by
  apply periodicDistribution_ext (isPeriodTwoDistribution_weightedDistributionSynthesis w hw a) hT
  intro n
  simpa only [weightedDistributionSynthesis_coefficientTest] using ha n

/-- Exact weighted regularity characterization for actual periodic tempered distributions. -/
theorem periodicDistribution_weighted_memlp_iff_existsUnique
    (w : Weight) (hw : w.HasTemperedInverse) (T : 𝓢'(ℝ, ℂ)) :
    (IsPeriodTwoDistribution T ∧ Memℓp (fun n : ℤ => (w n : ℂ) * T (coefficientTest n)) p) ↔
      ∃! a : WeightedCoeff w p, weightedDistributionSynthesis w hw a = T := by
  constructor
  · rintro ⟨hT, ha⟩
    let a : WeightedCoeff w p := ⟨fun n => T (coefficientTest n), ha⟩
    have he : weightedDistributionSynthesis w hw a = T :=
      weightedDistributionSynthesis_eq_of_periodic_coefficients w hw hT a (fun _ => rfl)
    refine ⟨a, he, fun b hb => ?_⟩
    exact weightedDistributionSynthesis_injective w hw (hb.trans he.symm)
  · rintro ⟨a, ha, _⟩
    rw [← ha]
    refine ⟨isPeriodTwoDistribution_weightedDistributionSynthesis w hw a, ?_⟩
    simp only [weightedDistributionSynthesis_coefficientTest]
    exact a.property

/-- Continuous distributional synthesis on the full real Sobolev regularity scale. -/
def sobolevDistributionSynthesisCLM (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] 𝓢'(ℝ, ℂ) :=
  weightedDistributionSynthesisCLM (Weight.sobolev s) (Weight.hasTemperedInverse_sobolev s)

/-- The raw Fourier sum is unchanged at negative or fractional regularity. -/
@[simp] theorem sobolevDistributionSynthesisCLM_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (g : 𝓢(ℝ, ℂ)) :
    sobolevDistributionSynthesisCLM s a g = ∑' n : ℤ, a.val n * (𝓕 g) (-(n : ℝ) / 2) :=
  weightedDistributionSynthesis_apply _ _ a g

/-- Every coefficient of the original Sobolev data is recovered exactly. -/
@[simp] theorem sobolevDistributionSynthesisCLM_coefficientTest (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    sobolevDistributionSynthesisCLM s a (coefficientTest n) = a.val n :=
  weightedDistributionSynthesis_coefficientTest _ _ a n

/-- Any real Sobolev regularity is intrinsically characterized by its actual Fourier coefficients. -/
theorem periodicDistribution_sobolev_memlp_iff_existsUnique (s : ℝ) (T : 𝓢'(ℝ, ℂ)) :
    (IsPeriodTwoDistribution T ∧
      Memℓp (fun n : ℤ => (((1 + |(n : ℝ)|) ^ s : ℝ) : ℂ) * T (coefficientTest n)) p) ↔
      ∃! a : WeightedCoeff (Weight.sobolev s) p, sobolevDistributionSynthesisCLM s a = T :=
  periodicDistribution_weighted_memlp_iff_existsUnique _ (Weight.hasTemperedInverse_sobolev s) T

/-- Sobolev truncations converge as actual distributions at every real regularity and Banach exponent. -/
theorem tendsto_sobolevDistributionSynthesis_truncate (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    Filter.Tendsto
      (fun S : Finset ℤ => sobolevDistributionSynthesisCLM s
        (WeightedCoeff.truncate (Weight.sobolev s) p S a))
      Filter.atTop (nhds (sobolevDistributionSynthesisCLM s a)) :=
  tendsto_weightedDistributionSynthesis_truncate _ (Weight.hasTemperedInverse_sobolev s) a

end NLS.Fourier
