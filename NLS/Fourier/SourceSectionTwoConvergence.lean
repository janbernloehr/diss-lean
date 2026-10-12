import NLS.SequenceSpaces.InfinityTruncation
import NLS.Fourier.WeightedDistributionIdentification

/-! # Section 2's Fourier convergence and its infinity-endpoint correction

The inverse Sobolev weight gives a genuine periodic distribution at every real
regularity. All its finite Fourier sums have norm error one, although they
converge distributionally. This refutes the unqualified norm-convergence
sentence on printed page 21, without changing the finite-exponent result.
-/
noncomputable section
open Filter Topology
open scoped ENNReal SchwartzMap
namespace NLS.Fourier

/-- A periodic distribution whose weighted Fourier coefficients are all one. -/
def sourceSectionTwoInfinityDistribution (s : ℝ) : 𝓢'(ℝ, ℂ) :=
  sobolevDistributionSynthesisCLM s
    (WeightedCoeff.inverseWeightCoefficients (Weight.sobolev s))

/-- The counterexample is a genuine period-two tempered distribution. -/
theorem sourceSectionTwoInfinityDistribution_periodic (s : ℝ) :
    IsPeriodTwoDistribution (sourceSectionTwoInfinityDistribution s) :=
  isPeriodTwoDistribution_weightedDistributionSynthesis _ _ _

/-- Its actual Fourier coefficients are (1+|n|)^(-s), for every real s. -/
theorem sourceSectionTwoInfinityDistribution_coefficient (s : ℝ) (n : ℤ) :
    sourceSectionTwoInfinityDistribution s (coefficientTest n) =
      (((1+|(n : ℝ)|)^s : ℝ) : ℂ)⁻¹ := by
  simp only [sourceSectionTwoInfinityDistribution,
    sobolevDistributionSynthesisCLM_coefficientTest,
    WeightedCoeff.inverseWeightCoefficients_val,Weight.sobolev_apply]

/-- The actual distribution has unit Fourier norm and constant truncation error,
while the same finite Fourier sums converge in the distribution topology. -/
theorem sourceSectionTwo_infinity_counterexample (s : ℝ) :
    ∃ a : WeightedCoeff (Weight.sobolev s) ⊤,
      sobolevDistributionSynthesisCLM s a = sourceSectionTwoInfinityDistribution s ∧
      ‖a‖ = 1 ∧
      (∀ S : Finset ℤ, ‖a-WeightedCoeff.truncate (Weight.sobolev s) ⊤ S a‖ = 1) ∧
      ¬Tendsto (fun S : Finset ℤ => WeightedCoeff.truncate (Weight.sobolev s) ⊤ S a)
        atTop (𝓝 a) ∧
      Tendsto (fun S : Finset ℤ => sobolevDistributionSynthesisCLM s
          (WeightedCoeff.truncate (Weight.sobolev s) ⊤ S a))
        atTop (𝓝 (sourceSectionTwoInfinityDistribution s)) := by
  refine ⟨WeightedCoeff.inverseWeightCoefficients (Weight.sobolev s),rfl,
    WeightedCoeff.norm_inverseWeightCoefficients _,
    WeightedCoeff.norm_inverseWeightCoefficients_sub_truncate _,
    WeightedCoeff.not_tendsto_truncate_inverseWeightCoefficients _,?_⟩
  exact tendsto_sobolevDistributionSynthesis_truncate s _

/-- The finite-exponent correction preserves every real Sobolev order, including negative orders. -/
theorem sourceSectionTwo_norm_convergence (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    Tendsto (fun S : Finset ℤ => WeightedCoeff.truncate (Weight.sobolev s) p S a)
      atTop (𝓝 a) :=
  WeightedCoeff.tendsto_truncate _ _ hp a

end NLS.Fourier
