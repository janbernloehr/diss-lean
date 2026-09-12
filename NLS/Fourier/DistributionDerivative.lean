import NLS.Fourier.DistributionPeriodicity
import NLS.Fourier.SobolevSynthesis

/-!
# Distributional differentiation and the exact Fourier domain

The actual derivative of a synthesized tempered distribution multiplies its
Fourier coefficients by `iπn`. Belonging to the one-derivative coefficient
domain is equivalent to having a distributional derivative represented in the
same `ℓᵖ` space. The statement includes the infinity endpoint.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
open ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Fourier samples of a differentiated Schwartz test have the dual sign. -/
theorem fourier_sample_deriv (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    (𝓕 (SchwartzMap.derivCLM ℂ ℂ g)) (-(n : ℝ) / 2) =
      -(Complex.I * (Real.pi : ℂ) * n) * (𝓕 g) (-(n : ℝ) / 2) := by
  change (𝓕 (deriv (g : ℝ → ℂ))) (-(n : ℝ) / 2) = _
  rw [Real.fourier_deriv g.integrable g.differentiable
    (SchwartzMap.derivCLM ℂ ℂ g).integrable]
  simp only [smul_eq_mul, ← SchwartzMap.fourier_coe]
  push_cast
  ring

/-- Differentiating the distribution gives the expected Fourier multiplier. -/
theorem distributionDerivative_apply (a : Coeff p) (g : 𝓢(ℝ, ℂ)) :
    TemperedDistribution.derivCLM ℂ (distributionSynthesis a) g =
      ∑' n : ℤ, (Complex.I * (Real.pi : ℂ) * n * a n) * (𝓕 g) (-(n : ℝ) / 2) := by
  rw [TemperedDistribution.derivCLM_apply_apply, distributionSynthesis_apply]
  simp only [FourierTransform.fourier_neg, neg_apply, fourier_sample_deriv]
  apply tsum_congr
  intro n
  ring

/-- Coefficient recovery applies to the actual distributional derivative of any input. -/
@[simp] theorem distributionDerivative_coefficientTest (a : Coeff p) (n : ℤ) :
    TemperedDistribution.derivCLM ℂ (distributionSynthesis a) (coefficientTest n) =
      Complex.I * (Real.pi : ℂ) * n * a n := by
  classical
  rw [distributionDerivative_apply, coefficientTest, FourierTransform.fourier_fourierInv_eq]
  simp [frequencyTest_sample]

/-- Equality to a prescribed distributional derivative is exactly the coefficient identity. -/
theorem distributionDerivative_eq_iff (a b : Coeff p) :
    TemperedDistribution.derivCLM ℂ (distributionSynthesis a) = distributionSynthesis b ↔
      ∀ n : ℤ, b n = Complex.I * (Real.pi : ℂ) * n * a n := by
  constructor
  · intro h n
    have he := congrArg (fun T : 𝓢'(ℝ, ℂ) => T (coefficientTest n)) h
    simpa only [distributionDerivative_coefficientTest, distributionSynthesis_coefficientTest]
      using he.symm
  · intro h
    ext g
    rw [distributionDerivative_apply, distributionSynthesis_apply]
    exact tsum_congr (fun n => by rw [h n])

/-- The existing derivative on the one-derivative domain is the genuine distribution derivative. -/
theorem distributionSynthesis_derivative (f : ScalarDomain p) :
    distributionSynthesis (derivative f) =
      TemperedDistribution.derivCLM ℂ (distributionSynthesis (scalarInclusion f)) := by
  apply ((distributionDerivative_eq_iff _ _).mpr ?_).symm
  intro n
  simp

/-- Exact graph identification: distributional differentiation gives precisely the existing domain. -/
theorem distributionDerivative_graph_iff (a b : Coeff p) :
    TemperedDistribution.derivCLM ℂ (distributionSynthesis a) = distributionSynthesis b ↔
      ∃ f : ScalarDomain p, scalarInclusion f = a ∧ derivative f = b := by
  constructor
  · intro h
    have hc := (distributionDerivative_eq_iff a b).mp h
    have hd : Memℓp (fun n : ℤ => Complex.I * (Real.pi : ℂ) * n * a n) p := by
      simpa only [← hc] using lp.memℓp b
    let f : ScalarDomain p := ⟨a, memlp_sobolev_weight_of_derivative (lp.memℓp a) hd⟩
    refine ⟨f, ?_, ?_⟩
    · ext n
      exact scalarInclusion_apply f n
    · ext n
      exact (hc n).symm
  · rintro ⟨f, rfl, rfl⟩
    exact (distributionSynthesis_derivative f).symm

/-- The distributional derivative stays in the same Fourier class exactly on the scalar domain. -/
theorem distributionDerivative_exists_iff (a : Coeff p) :
    (∃ b : Coeff p, TemperedDistribution.derivCLM ℂ (distributionSynthesis a) =
      distributionSynthesis b) ↔ a ∈ LinearMap.range (scalarInclusion (p := p)).toLinearMap := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨f, hf, _⟩ := (distributionDerivative_graph_iff a b).mp hb
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    exact ⟨derivative f, (distributionSynthesis_derivative f).symm⟩

/-- The domain derivative obeys integration by parts on genuine Schwartz tests. -/
theorem distributionSynthesis_derivative_apply (f : ScalarDomain p) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (derivative f) g =
      -distributionSynthesis (scalarInclusion f) (SchwartzMap.derivCLM ℂ ℂ g) := by
  rw [distributionSynthesis_derivative, TemperedDistribution.derivCLM_apply_apply, map_neg]

/-- Synthesis identifies the domain's included distribution with its continuous representative. -/
theorem distributionSynthesis_scalarInclusion (hp : p ≠ ⊤) (f : ScalarDomain p)
    (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (scalarInclusion f) g =
      ∫ x : ℝ, sobolevSynthesis hp f (x : AddCircle (2 : ℝ)) * g x := by
  have he : distributionSynthesis (scalarInclusion f) =
      distributionSynthesis (WeightedCoeff.sobolevToL1CLM p hp f) := by
    apply (distributionSynthesis_eq_iff _ _).mpr
    intro n
    simp [WeightedCoeff.sobolevToL1CLM_apply]
  rw [he, distributionSynthesis_eq_integral_continuousSynthesis]
  rfl

/-- The derivative of the actual continuous representative satisfies weak integration by parts. -/
theorem distributionSynthesis_derivative_eq_integral (hp : p ≠ ⊤) (f : ScalarDomain p)
    (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (derivative f) g =
      -(∫ x : ℝ, sobolevSynthesis hp f (x : AddCircle (2 : ℝ)) * deriv g x) := by
  rw [distributionSynthesis_derivative_apply, distributionSynthesis_scalarInclusion hp]
  rfl

/-- Closedness follows directly from the actual distributional derivative graph. -/
theorem isClosed_distributionDerivativeGraph :
    IsClosed {ab : Coeff p × Coeff p |
      ∃ f : ScalarDomain p, scalarInclusion f = ab.1 ∧ derivative f = ab.2} := by
  simp_rw [← distributionDerivative_graph_iff]
  exact isClosed_eq
    ((TemperedDistribution.derivCLM ℂ).continuous.comp
      (distributionSynthesisCLM.continuous.comp continuous_fst))
    (distributionSynthesisCLM.continuous.comp continuous_snd)

end NLS.Fourier
