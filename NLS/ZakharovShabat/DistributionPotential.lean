import NLS.Fourier.DistributionProduct
import NLS.ZakharovShabat.DistributionFreeOperator

/-!
# The Zakharov–Shabat potential and operator on actual distributions

On the one-derivative domain, potential multiplication is the unique continuous
extension of genuine smooth distribution multiplication. Its action is given
by actual real-line integrals against the continuous Sobolev representative.
The resulting signed derivative plus off-diagonal product agrees with the
existing coefficient operator, including its eigenvalue equations.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.ZakharovShabat
open NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Multiplication of a Fourier-class distribution by a one-derivative domain element. -/
def distributionPotentialMul (hp : p ≠ ⊤) (φ : Coeff p) : ScalarDomain p →L[ℂ] 𝓢'(ℝ, ℂ) :=
  (distributionProductCLM φ).comp (WeightedCoeff.sobolevToL1CLM p hp)

/-- The extended distribution product realizes the existing coefficient potential exactly. -/
@[simp] theorem distributionPotentialMul_eq (hp : p ≠ ⊤) (φ : Coeff p) (f : ScalarDomain p) :
    distributionPotentialMul hp φ f = distributionSynthesis (potentialMul hp φ f) := rfl

/-- The product tests the potential against the actual continuous domain representative. -/
theorem distributionPotentialMul_apply_integrals (hp : p ≠ ⊤) (φ : Coeff p) (f : ScalarDomain p)
    (g : 𝓢(ℝ, ℂ)) :
    distributionPotentialMul hp φ f g = ∑' n : ℤ, φ n *
      ∫ x : ℝ, wave n x * (sobolevSynthesis hp f (x : AddCircle (2 : ℝ)) * g x) :=
  distributionProduct_apply_integrals φ (WeightedCoeff.sobolevToL1CLM p hp f) g

/-- The physical test-integral formula is absolutely convergent. -/
theorem summable_norm_distributionPotentialMul_integrals (hp : p ≠ ⊤)
    (φ : Coeff p) (f : ScalarDomain p) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖φ n *
      ∫ x : ℝ, wave n x * (sobolevSynthesis hp f (x : AddCircle (2 : ℝ)) * g x)‖) :=
  summable_norm_distributionProduct_integrals φ (WeightedCoeff.sobolevToL1CLM p hp f) g

/-- Quantitative control in the source's scalar domain norm. -/
theorem norm_distributionPotentialMul_apply_le (hp : p ≠ ⊤) (φ : Coeff p) (f : ScalarDomain p)
    (g : 𝓢(ℝ, ℂ)) :
    ‖distributionPotentialMul hp φ f g‖ ≤
      (WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖ * ‖f‖) * ‖schwartzSamples (𝓕 g)‖ :=
  (norm_distributionSynthesis_apply_le _ g).trans
    (mul_le_mul_of_nonneg_right (norm_potentialMul_apply_le hp φ f) (norm_nonneg _))

private theorem fourierPolynomial_sobolevToL1 (hp : p ≠ ⊤) (f : ScalarDomain p) (s : Finset ℤ) :
    fourierPolynomial s (WeightedCoeff.sobolevToL1CLM p hp f) = fourierPolynomial s f.val := by
  funext x
  simp only [fourierPolynomial, WeightedCoeff.sobolevToL1CLM_apply]

/-- Canonical smooth Fourier multipliers converge to multiplication on the full domain. -/
theorem tendsto_distributionPotentialMul_polynomials (hp : p ≠ ⊤) (φ : Coeff p) (f : ScalarDomain p) :
    Filter.Tendsto (fun s : Finset ℤ => TemperedDistribution.smulLeftCLM ℂ
      (fourierPolynomial s f.val) (distributionSynthesis φ))
      Filter.atTop (nhds (distributionPotentialMul hp φ f)) := by
  have h := tendsto_polynomial_distributionProduct φ (WeightedCoeff.sobolevToL1CLM p hp f)
  simp_rw [fourierPolynomial_sobolevToL1 hp f] at h
  exact h

/-- On a finite Fourier domain element, multiplication is Mathlib's actual smooth operation. -/
theorem distributionPotentialMul_of_finiteSupport (hp : p ≠ ⊤) (φ : Coeff p) (f : ScalarDomain p)
    (s : Finset ℤ) (hf : ∀ n ∉ s, f.val n = 0) :
    distributionPotentialMul hp φ f = TemperedDistribution.smulLeftCLM ℂ
      (fourierPolynomial s f.val) (distributionSynthesis φ) := by
  have ht : Coeff.truncate s (WeightedCoeff.sobolevToL1CLM p hp f) =
      WeightedCoeff.sobolevToL1CLM p hp f := by
    ext n
    by_cases hn : n ∈ s <;> simp [Coeff.truncate_apply, hn, WeightedCoeff.sobolevToL1CLM_apply, hf]
  have h := distributionProduct_truncate φ (WeightedCoeff.sobolevToL1CLM p hp f) s
  rw [ht] at h
  simp_rw [fourierPolynomial_sobolevToL1 hp f] at h
  exact h

/-- Arbitrary converging finite Fourier approximations give the same distribution product. -/
theorem tendsto_distributionPotentialMul_smooth_approximation (hp : p ≠ ⊤)
    {ι : Type*} {l : Filter ι} {φᵢ : ι → Coeff p} {fᵢ : ι → ScalarDomain p}
    {φ : Coeff p} {f : ScalarDomain p} (s : ι → Finset ℤ)
    (hs : ∀ i n, n ∉ s i → (fᵢ i).val n = 0)
    (hφ : Filter.Tendsto φᵢ l (nhds φ)) (hf : Filter.Tendsto fᵢ l (nhds f)) :
    Filter.Tendsto (fun i => TemperedDistribution.smulLeftCLM ℂ
      (fourierPolynomial (s i) (fᵢ i).val) (distributionSynthesis (φᵢ i))) l
      (nhds (distributionPotentialMul hp φ f)) := by
  have h := tendsto_distributionProduct hφ
    (((WeightedCoeff.sobolevToL1CLM p hp).continuous.tendsto f).comp hf)
  change Filter.Tendsto (fun i => distributionPotentialMul hp (φᵢ i) (fᵢ i)) l
    (nhds (distributionPotentialMul hp φ f)) at h
  simpa only [distributionPotentialMul_of_finiteSupport hp _ _ _ (hs _)] using h

/-- The actual off-diagonal potential matrix, using the proved extended distribution products. -/
def distributionPotentialOperator (hp : p ≠ ⊤) (φ : PairSpace p) :
    Domain p →L[ℂ] 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  ((distributionPotentialMul hp φ.1).comp (ContinuousLinearMap.snd ℂ _ _)).prod
    ((distributionPotentialMul hp φ.2).comp (ContinuousLinearMap.fst ℂ _ _))

@[simp] theorem distributionPotentialOperator_eq (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) :
    distributionPotentialOperator hp φ f = distributionPairCLM (potentialOperator hp φ f) := by
  change (distributionPotentialMul hp φ.1 f.2, distributionPotentialMul hp φ.2 f.1) =
    (distributionSynthesis (potentialMul hp φ.1 f.2), distributionSynthesis (potentialMul hp φ.2 f.1))
  exact Prod.ext (distributionPotentialMul_eq hp φ.1 f.2) (distributionPotentialMul_eq hp φ.2 f.1)

/-- The full physical differential expression `diag(i,-i)D + [[0,φ₁],[φ₂,0]]`. -/
def distributionOperator (hp : p ≠ ⊤) (φ : PairSpace p) :
    Domain p →L[ℂ] 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  distributionFreeOperator.comp (distributionPairCLM.comp domainInclusion) +
    distributionPotentialOperator hp φ

/-- The existing coefficient operator exactly realizes the full distributional expression. -/
theorem distributionOperator_eq (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) :
    distributionOperator hp φ f = distributionPairCLM (operator hp φ f) := by
  change distributionFreeOperator (distributionPairCLM (domainInclusion f)) +
    distributionPotentialOperator hp φ f = _
  rw [← distributionPairCLM_freeOperator, distributionPotentialOperator_eq, ← map_add]
  rfl

/-- Equality of the full distributional equation is faithfully reflected in coefficients. -/
theorem distributionOperator_eq_iff (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) (b : PairSpace p) :
    distributionOperator hp φ f = distributionPairCLM b ↔ operator hp φ f = b := by
  rw [distributionOperator_eq]
  exact distributionPairCLM_injective.eq_iff

/-- Distributional eigenvalue equations coincide exactly with the previously analyzed operator. -/
theorem distributional_eigen_equation_iff (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) (z : ℂ) :
    distributionOperator hp φ f = z • distributionPairCLM (domainInclusion f) ↔
      operator hp φ f = z • domainInclusion f := by
  rw [← map_smul, distributionOperator_eq_iff]

end NLS.ZakharovShabat
