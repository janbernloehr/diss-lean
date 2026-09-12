import NLS.Fourier.WeightedSchwartzSampling
import NLS.Fourier.PeriodicDistributionIdentification

/-!
# Weighted Fourier data as genuine periodic distributions

A positive weight with polynomially bounded reciprocal gives a continuous
injective synthesis of its Banach coefficient space into actual tempered
distributions. The action uses the raw coefficients, independently of the
chosen weight, growth bound, or exponent.
-/

noncomputable section
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted data synthesized as an actual complex-linear tempered distribution. -/
def weightedDistributionSynthesis (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) : 𝓢'(ℝ, ℂ) :=
  (Coeff.testFunctional (WeightedCoeff.weightEquiv w p a)).comp
    ((weightedSchwartzSamplesCLM w hw).comp (FourierTransform.fourierCLM ℂ 𝓢(ℝ, ℂ)))

omit [Fact (1 ≤ p)] in
private theorem weighted_pair_term (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    WeightedCoeff.weightEquiv w p a n * weightedSchwartzSamples w hw (𝓕 g) n =
      a.val n * (𝓕 g) (-(n : ℝ) / 2) := by
  rw [WeightedCoeff.weightEquiv_apply, weightedSchwartzSamples_apply]
  field_simp [w.complex_ne_zero n]

/-- Absolute convergence of the raw-coefficient distributional action. -/
theorem summable_norm_weightedDistributionSynthesis (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖a.val n * (𝓕 g) (-(n : ℝ) / 2)‖) := by
  simpa only [weighted_pair_term] using Coeff.summable_norm_testPairing
    (WeightedCoeff.weightEquiv w p a) (weightedSchwartzSamples w hw (𝓕 g))

/-- The weight cancels from the actual Fourier action. -/
@[simp] theorem weightedDistributionSynthesis_apply (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) (g : 𝓢(ℝ, ℂ)) :
    weightedDistributionSynthesis w hw a g = ∑' n : ℤ, a.val n * (𝓕 g) (-(n : ℝ) / 2) := by
  change (∑' n : ℤ, WeightedCoeff.weightEquiv w p a n * weightedSchwartzSamples w hw (𝓕 g) n) = _
  exact tsum_congr (weighted_pair_term w hw a g)

/-- The weighted coefficient norm controls the action on each Schwartz test. -/
theorem norm_weightedDistributionSynthesis_apply_le (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) (g : 𝓢(ℝ, ℂ)) :
    ‖weightedDistributionSynthesis w hw a g‖ ≤ ‖a‖ * ‖weightedSchwartzSamples w hw (𝓕 g)‖ :=
  Coeff.norm_testPairing_le (WeightedCoeff.weightEquiv w p a) (weightedSchwartzSamples w hw (𝓕 g))

/-- Synthesis depends continuously and linearly on the original weighted coefficient data. -/
def weightedDistributionSynthesisCLM (w : Weight) (hw : w.HasTemperedInverse) :
    WeightedCoeff w p →L[ℂ] 𝓢'(ℝ, ℂ) where
  toFun := weightedDistributionSynthesis w hw
  map_add' a b := by
    ext g
    change Coeff.testFunctional (WeightedCoeff.weightEquiv w p (a + b))
      (weightedSchwartzSamples w hw (𝓕 g)) = _
    rw [map_add, Coeff.testFunctional_add]
    rfl
  map_smul' c a := by
    ext g
    change Coeff.testFunctional (WeightedCoeff.weightEquiv w p (c • a))
      (weightedSchwartzSamples w hw (𝓕 g)) = _
    rw [map_smul, Coeff.testFunctional_smul]
    rfl
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval fun g =>
    ((ContinuousLinearMap.apply ℂ ℂ (weightedSchwartzSamples w hw (𝓕 g))).continuous.comp
      Coeff.testDualityCLM.continuous).comp (WeightedCoeff.weightIsometry w p).continuous

@[simp] theorem weightedDistributionSynthesisCLM_apply (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) : weightedDistributionSynthesisCLM w hw a = weightedDistributionSynthesis w hw a := rfl

/-- The same localized Schwartz tests recover every raw weighted coefficient. -/
@[simp] theorem weightedDistributionSynthesis_coefficientTest (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) (n : ℤ) : weightedDistributionSynthesis w hw a (coefficientTest n) = a.val n := by
  classical
  rw [weightedDistributionSynthesis_apply, coefficientTest, FourierTransform.fourier_fourierInv_eq]
  simp [frequencyTest_sample]

/-- Weighted synthesis is injective on the original raw coefficient sequences. -/
theorem weightedDistributionSynthesis_injective (w : Weight) (hw : w.HasTemperedInverse) :
    Function.Injective (weightedDistributionSynthesis (p := p) w hw) := by
  intro a b h
  apply Subtype.ext
  funext n
  simpa only [weightedDistributionSynthesis_coefficientTest] using
    congrArg (fun T : 𝓢'(ℝ, ℂ) => T (coefficientTest n)) h

/-- Every synthesized weighted sequence is intrinsically period two. -/
theorem isPeriodTwoDistribution_weightedDistributionSynthesis (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) : IsPeriodTwoDistribution (weightedDistributionSynthesis w hw a) := by
  intro g
  simp only [weightedDistributionSynthesis_apply, fourier_sample_translate]
  apply tsum_congr
  intro n
  have he : wave n 2 = 1 := by
    convert wave_even_at_one n using 1
    unfold wave
    congr 1
    push_cast
    ring
  rw [he, one_mul]

/-- Finite truncations converge as distributions even at infinity and at negative regularity. -/
theorem tendsto_weightedDistributionSynthesis_truncate (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) :
    Filter.Tendsto (fun s : Finset ℤ => weightedDistributionSynthesis w hw (WeightedCoeff.truncate w p s a))
      Filter.atTop (nhds (weightedDistributionSynthesis w hw a)) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro g
  change Filter.Tendsto (fun s : Finset ℤ => weightedDistributionSynthesis w hw (WeightedCoeff.truncate w p s a) g)
    Filter.atTop (nhds (weightedDistributionSynthesis w hw a g))
  simp only [weightedDistributionSynthesis_apply, WeightedCoeff.truncate_apply, ite_mul, zero_mul]
  have he (s : Finset ℤ) (b : ℤ → ℂ) : (∑' n : ℤ, if n ∈ s then b n else 0) =
      ∑ n ∈ s, b n := by
    classical
    rw [tsum_eq_sum (s := s) (by intro n hn; simp [hn])]
    exact Finset.sum_congr rfl (fun n hn => if_pos hn)
  simp_rw [he]
  exact (summable_norm_weightedDistributionSynthesis w hw a g).of_norm.hasSum

/-- Equal raw coefficients give the same actual distribution across weights and exponents. -/
theorem weightedDistributionSynthesis_eq_iff {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (w v : Weight) (hw : w.HasTemperedInverse) (hv : v.HasTemperedInverse)
    (a : WeightedCoeff w p) (b : WeightedCoeff v q) :
    weightedDistributionSynthesis w hw a = weightedDistributionSynthesis v hv b ↔
      ∀ n : ℤ, a.val n = b.val n := by
  constructor
  · intro h n
    simpa only [weightedDistributionSynthesis_coefficientTest] using
      congrArg (fun T : 𝓢'(ℝ, ℂ) => T (coefficientTest n)) h
  · intro h
    ext g
    simp only [weightedDistributionSynthesis_apply]
    exact tsum_congr (fun n => by rw [h n])

/-- Weighted synthesis agrees with the existing unweighted realization whenever raw data agrees. -/
theorem weightedDistributionSynthesis_eq_distributionSynthesis {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (w : Weight) (hw : w.HasTemperedInverse) (a : WeightedCoeff w p) (b : Coeff q)
    (h : ∀ n : ℤ, a.val n = b n) : weightedDistributionSynthesis w hw a = distributionSynthesis b := by
  ext g
  simp only [weightedDistributionSynthesis_apply, distributionSynthesis_apply]
  exact tsum_congr (fun n => by rw [h n])

end NLS.Fourier
