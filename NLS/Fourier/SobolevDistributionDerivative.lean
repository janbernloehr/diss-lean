import NLS.Fourier.WeightedDistributionIdentification
import NLS.Fourier.DistributionDerivative
import NLS.SequenceSpaces.SobolevDerivative

/-!
# Exact distributional derivative domains at every real regularity

Regularity embeddings preserve the represented distribution. The coefficient
derivative agrees with Mathlib's actual tempered-distribution derivative, and
its closed graph has precisely the next Sobolev space as its domain.
-/

noncomputable section
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
open WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A monotone weight inclusion leaves the actual distribution unchanged. -/
theorem weightedDistributionSynthesis_inclusion (w v : Weight)
    (hw : w.HasTemperedInverse) (hv : v.HasTemperedInverse) (h : ∀ n, v n ≤ w n)
    (a : WeightedCoeff w p) :
    weightedDistributionSynthesis v hv (inclusionCLM w v h a) =
      weightedDistributionSynthesis w hw a :=
  (weightedDistributionSynthesis_eq_iff _ _ _ _ _ _).mpr
    (fun n => inclusionCLM_apply w v h a n)

/-- Lowering real Sobolev regularity keeps the same distribution. -/
theorem sobolevDistributionSynthesis_inclusion {s t : ℝ} (h : t ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    sobolevDistributionSynthesisCLM t (sobolevInclusion h a) =
      sobolevDistributionSynthesisCLM s a :=
  weightedDistributionSynthesis_inclusion _ _ _ _ _ a

/-- The actual derivative acts by the period-two Fourier symbol at every regularity. -/
theorem sobolevDistributionDerivative_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (g : 𝓢(ℝ, ℂ)) :
    TemperedDistribution.derivCLM ℂ (sobolevDistributionSynthesisCLM s a) g =
      ∑' n : ℤ, (Complex.I * (Real.pi : ℂ) * n * a.val n) *
        (𝓕 g) (-(n : ℝ) / 2) := by
  rw [TemperedDistribution.derivCLM_apply_apply, sobolevDistributionSynthesisCLM_apply]
  simp only [FourierTransform.fourier_neg, neg_apply, fourier_sample_deriv]
  apply tsum_congr
  intro n
  ring

@[simp] theorem sobolevDistributionDerivative_coefficientTest (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    TemperedDistribution.derivCLM ℂ (sobolevDistributionSynthesisCLM s a)
      (coefficientTest n) = Complex.I * (Real.pi : ℂ) * n * a.val n := by
  classical
  rw [sobolevDistributionDerivative_apply, coefficientTest,
    FourierTransform.fourier_fourierInv_eq]
  simp [frequencyTest_sample]

/-- Distributional derivative equality is equivalent to the raw symbol identity. -/
theorem sobolevDistributionDerivative_eq_iff (s t : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev t) p) :
    TemperedDistribution.derivCLM ℂ (sobolevDistributionSynthesisCLM s a) =
      sobolevDistributionSynthesisCLM t b ↔
      ∀ n : ℤ, b.val n = Complex.I * (Real.pi : ℂ) * n * a.val n := by
  constructor
  · intro h n
    have he := congrArg (fun T : 𝓢'(ℝ, ℂ) => T (coefficientTest n)) h
    simpa only [sobolevDistributionDerivative_coefficientTest,
      sobolevDistributionSynthesisCLM_coefficientTest] using he.symm
  · intro h
    ext g
    rw [sobolevDistributionDerivative_apply, sobolevDistributionSynthesisCLM_apply]
    exact tsum_congr (fun n => by rw [h n])

/-- The coefficient derivative is the genuine derivative, with loss of one regularity unit. -/
theorem sobolevDistributionSynthesis_derivative (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev (s + 1)) p) :
    sobolevDistributionSynthesisCLM s (WeightedCoeff.sobolevDerivative s a) =
      TemperedDistribution.derivCLM ℂ (sobolevDistributionSynthesisCLM (s + 1) a) := by
  apply ((sobolevDistributionDerivative_eq_iff _ _ _ _).mpr ?_).symm
  intro n
  exact sobolevDerivative_apply s a n

/-- Exact derivative graph and domain, including negative regularity and the infinity endpoint. -/
theorem sobolevDistributionDerivative_graph_iff (s : ℝ)
    (a b : WeightedCoeff (Weight.sobolev s) p) :
    TemperedDistribution.derivCLM ℂ (sobolevDistributionSynthesisCLM s a) =
      sobolevDistributionSynthesisCLM s b ↔
      ∃ f : WeightedCoeff (Weight.sobolev (s + 1)) p,
        sobolevInclusion (le_add_of_nonneg_right zero_le_one) f = a ∧
        WeightedCoeff.sobolevDerivative s f = b := by
  constructor
  · intro h
    have hc := (sobolevDistributionDerivative_eq_iff s s a b).mp h
    have hd : Memℓp (fun n => (Weight.sobolev s n : ℂ) *
        (Complex.I * (Real.pi : ℂ) * n * a.val n)) p := by
      have hb := b.property
      change Memℓp (fun n => (Weight.sobolev s n : ℂ) * b.val n) p at hb
      simpa only [← hc] using hb
    let f : WeightedCoeff (Weight.sobolev (s + 1)) p :=
      ⟨a.val, memlp_sobolev_succ_of_derivative s a.property hd⟩
    refine ⟨f, ?_, ?_⟩
    · apply Subtype.ext
      funext n
      exact sobolevInclusion_apply _ f n
    · apply Subtype.ext
      funext n
      exact (hc n).symm
  · rintro ⟨f, rfl, rfl⟩
    rw [sobolevDistributionSynthesis_inclusion]
    exact (sobolevDistributionSynthesis_derivative s f).symm

/-- Differentiation is closed in each Sobolev coefficient norm. -/
theorem isClosed_sobolevDistributionDerivativeGraph (s : ℝ) :
    IsClosed {ab : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p |
      ∃ f : WeightedCoeff (Weight.sobolev (s + 1)) p,
        sobolevInclusion (le_add_of_nonneg_right zero_le_one) f = ab.1 ∧
        WeightedCoeff.sobolevDerivative s f = ab.2} := by
  simp_rw [← sobolevDistributionDerivative_graph_iff]
  exact isClosed_eq
    ((TemperedDistribution.derivCLM ℂ).continuous.comp
      ((sobolevDistributionSynthesisCLM s).continuous.comp continuous_fst))
    ((sobolevDistributionSynthesisCLM s).continuous.comp continuous_snd)

/-- Intrinsic regularity gain: a periodic distribution and its derivative in `s`
are equivalent to the distribution in `s+1`, without choosing a representation. -/
theorem periodicDistribution_sobolev_derivative_memlp_iff (s : ℝ)
    (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T) :
    (Memℓp (fun n : ℤ => (Weight.sobolev s n : ℂ) * T (coefficientTest n)) p ∧
      Memℓp (fun n : ℤ => (Weight.sobolev s n : ℂ) *
        (TemperedDistribution.derivCLM ℂ T) (coefficientTest n)) p) ↔
    Memℓp (fun n : ℤ => (Weight.sobolev (s + 1) n : ℂ) * T (coefficientTest n)) p := by
  constructor
  · rintro ⟨ha, hd⟩
    let a : WeightedCoeff (Weight.sobolev s) p := ⟨fun n => T (coefficientTest n), ha⟩
    have he : sobolevDistributionSynthesisCLM s a = T :=
      weightedDistributionSynthesis_eq_of_periodic_coefficients _ _ hT a (fun _ => rfl)
    have hc (n : ℤ) : (TemperedDistribution.derivCLM ℂ T) (coefficientTest n) =
        Complex.I * (Real.pi : ℂ) * n * T (coefficientTest n) := by
      rw [← he, sobolevDistributionDerivative_coefficientTest,
        sobolevDistributionSynthesisCLM_coefficientTest]
    exact memlp_sobolev_succ_of_derivative s ha (by simpa only [hc] using hd)
  · intro ha
    let a : WeightedCoeff (Weight.sobolev (s + 1)) p :=
      ⟨fun n => T (coefficientTest n), ha⟩
    have he : sobolevDistributionSynthesisCLM (s + 1) a = T :=
      weightedDistributionSynthesis_eq_of_periodic_coefficients _ _ hT a (fun _ => rfl)
    constructor
    · have hb := (sobolevInclusion (le_add_of_nonneg_right zero_le_one) a).property
      change Memℓp (fun n => (Weight.sobolev s n : ℂ) *
        (sobolevInclusion (le_add_of_nonneg_right zero_le_one) a).val n) p at hb
      simpa only [sobolevInclusion_apply] using hb
    · rw [← he, ← sobolevDistributionSynthesis_derivative]
      simp only [sobolevDistributionSynthesisCLM_coefficientTest]
      exact (WeightedCoeff.sobolevDerivative s a).property

end NLS.Fourier
