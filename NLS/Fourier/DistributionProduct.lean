import NLS.Fourier.ProductTestSamples

/-!
# The continuous extension of smooth distribution multiplication

Convolution realizes the unique continuous extension of multiplication by
Fourier polynomials to `ℓ¹` multiplier coefficients. Polynomial multiplication
is Mathlib's actual smooth distribution multiplication. The limit is independent
of the choice of approximation in `ℓ¹`, and depends continuously on both inputs.
This does not apply the totalized smooth-multiplier API to a nonsmooth function.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The continuous Fourier-regularity extension of smooth distribution multiplication. -/
def distributionProduct (a : Coeff p) (b : Coeff 1) : 𝓢'(ℝ, ℂ) :=
  distributionSynthesis (Coeff.convolution a b)

/-- Continuous linear dependence on the absolutely summable multiplier. -/
def distributionProductCLM (a : Coeff p) : Coeff 1 →L[ℂ] 𝓢'(ℝ, ℂ) :=
  distributionSynthesisCLM.comp (Coeff.convolutionCLM a)

@[simp] theorem distributionProductCLM_apply (a : Coeff p) (b : Coeff 1) :
    distributionProductCLM a b = distributionProduct a b := rfl

/-- The extension agrees with actual smooth multiplication on every Fourier polynomial. -/
theorem distributionProduct_truncate (a : Coeff p) (b : Coeff 1) (s : Finset ℤ) :
    distributionProduct a (Coeff.truncate s b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial s b) (distributionSynthesis a) :=
  distributionSynthesis_convolution_truncate a b s

/-- The canonical polynomial multipliers converge to the extended product as distributions. -/
theorem tendsto_polynomial_distributionProduct (a : Coeff p) (b : Coeff 1) :
    Filter.Tendsto (fun s : Finset ℤ =>
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial s b) (distributionSynthesis a))
      Filter.atTop (nhds (distributionProduct a b)) := by
  simp_rw [← distributionProduct_truncate]
  exact (distributionProductCLM a).continuous.tendsto b |>.comp (Coeff.tendsto_truncate (by simp) b)

/-- The extended product is jointly continuous in the two coefficient norms. -/
theorem continuous_distributionProduct :
    Continuous (fun ab : Coeff p × Coeff 1 => distributionProduct ab.1 ab.2) :=
  distributionSynthesisCLM.continuous.comp
    ((Coeff.convolutionCLM.continuous.comp continuous_fst).clm_apply continuous_snd)

/-- Every pair of converging coefficient approximations gives the same product limit. -/
theorem tendsto_distributionProduct {ι : Type*} {l : Filter ι}
    {aᵢ : ι → Coeff p} {bᵢ : ι → Coeff 1} {a : Coeff p} {b : Coeff 1}
    (ha : Filter.Tendsto aᵢ l (nhds a)) (hb : Filter.Tendsto bᵢ l (nhds b)) :
    Filter.Tendsto (fun i => distributionProduct (aᵢ i) (bᵢ i)) l
      (nhds (distributionProduct a b)) := by
  have hpair : Filter.Tendsto (fun i => (aᵢ i, bᵢ i)) l (nhds (a, b)) := ha.prodMk_nhds hb
  have hprod := (continuous_distributionProduct (p := p)).tendsto (a, b)
  simpa only [Function.comp_def] using! hprod.comp hpair

/-- A quantitative bound on every Schwartz test controls approximation errors. -/
theorem norm_distributionProduct_apply_le (a : Coeff p) (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    ‖distributionProduct a b g‖ ≤ (‖a‖ * ‖b‖) * ‖schwartzSamples (𝓕 g)‖ :=
  (norm_distributionSynthesis_apply_le _ g).trans
    (mul_le_mul_of_nonneg_right (Coeff.norm_convolution_le a b) (norm_nonneg _))

/-- No other continuous extension agreeing on all Fourier polynomials can give a different product. -/
theorem distributionProduct_unique (a : Coeff p) (F : Coeff 1 → 𝓢'(ℝ, ℂ))
    (hF : Continuous F)
    (hpoly : ∀ (b : Coeff 1) (s : Finset ℤ), F (Coeff.truncate s b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial s b) (distributionSynthesis a)) :
    F = distributionProduct a := by
  funext b
  have h₁ := (hF.tendsto b).comp (Coeff.tendsto_truncate (by simp) b)
  have h₂ := tendsto_polynomial_distributionProduct a b
  change Filter.Tendsto (fun s : Finset ℤ => F (Coeff.truncate s b)) Filter.atTop (nhds (F b)) at h₁
  simp_rw [hpoly] at h₁
  exact tendsto_nhds_unique h₁ h₂

/-- Extended multiplication has exactly the existing convolution coefficients. -/
@[simp] theorem distributionProduct_coefficientTest (a : Coeff p) (b : Coeff 1) (n : ℤ) :
    distributionProduct a b (coefficientTest n) = ∑' k : ℤ, a (n - k) * b k := by
  rw [distributionProduct, distributionSynthesis_coefficientTest, Coeff.convolution_apply]

/-- The product is the convergent series of actual smooth single-wave multiplications. -/
theorem hasSum_distributionProduct (a : Coeff p) (b : Coeff 1) :
    HasSum (fun k : ℤ => b k •
      TemperedDistribution.smulLeftCLM ℂ (wave k) (distributionSynthesis a))
      (distributionProduct a b) := by
  have h := (distributionSynthesisCLM (p := p)).hasSum (Coeff.summable_convolution_terms a b).hasSum
  simpa only [map_smul, distributionSynthesisCLM_apply, distributionSynthesis_shift,
    distributionProduct, Coeff.convolution] using h

/-- Extended multiplication acts by transposing the actual continuous multiplier onto tests. -/
theorem distributionProduct_apply_testPairing (a : Coeff p) (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    distributionProduct a b g = Coeff.testPairing a (productTestSamples b g) :=
  Coeff.testPairing_convolution a b (schwartzSamples (𝓕 g))

/-- The product action is an absolutely convergent series of actual real-line test integrals. -/
theorem distributionProduct_apply_integrals (a : Coeff p) (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    distributionProduct a b g = ∑' n : ℤ, a n *
      ∫ x : ℝ, wave n x * (continuousSynthesis b (x : AddCircle (2 : ℝ)) * g x) := by
  rw [distributionProduct_apply_testPairing, Coeff.testPairing]
  simp_rw [productTestSamples_eq_integral]

theorem summable_norm_distributionProduct_integrals (a : Coeff p) (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖a n *
      ∫ x : ℝ, wave n x * (continuousSynthesis b (x : AddCircle (2 : ℝ)) * g x)‖) := by
  simpa only [productTestSamples_eq_integral] using
    Coeff.summable_norm_testPairing a (productTestSamples b g)

/-- Every smooth multiplier in the Wiener class agrees with Mathlib's distribution multiplication. -/
theorem distributionProduct_eq_smooth_mul (a : Coeff p) (b : Coeff 1)
    (hb : (fun x : ℝ => continuousSynthesis b (x : AddCircle (2 : ℝ))).HasTemperateGrowth) :
    distributionProduct a b = TemperedDistribution.smulLeftCLM ℂ
      (fun x : ℝ => continuousSynthesis b (x : AddCircle (2 : ℝ))) (distributionSynthesis a) := by
  ext g
  rw [distributionProduct_apply_testPairing, productTestSamples_eq_smooth_samples b hb,
    TemperedDistribution.smulLeftCLM_apply_apply]
  rfl

/-- For absolutely summable potential data, the extension is ordinary multiplication of functions. -/
theorem distributionProduct_eq_integral (a b : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    distributionProduct a b g = ∫ x : ℝ,
      continuousSynthesis a (x : AddCircle (2 : ℝ)) *
        (continuousSynthesis b (x : AddCircle (2 : ℝ)) * g x) := by
  rw [distributionProduct_apply_integrals]
  exact tsum_integral_wave_eq_integral_synthesis a _ (integrable_synthesis_mul_test b g)

/-- The extension depends only on the actual potential distribution, not its chosen exponent. -/
theorem distributionProduct_eq_of_synthesis_eq {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a : Coeff p) (a' : Coeff q) (h : distributionSynthesis a = distributionSynthesis a')
    (b : Coeff 1) : distributionProduct a b = distributionProduct a' b := by
  have h₁ := tendsto_polynomial_distributionProduct a b
  have h₂ := tendsto_polynomial_distributionProduct a' b
  rw [h] at h₁
  exact tendsto_nhds_unique h₁ h₂

end NLS.Fourier
