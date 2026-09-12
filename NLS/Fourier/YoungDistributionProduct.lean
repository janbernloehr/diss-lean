import NLS.Fourier.DistributionProduct
import NLS.Fourier.PeriodicDistributionIdentification
import NLS.SequenceSpaces.YoungConvolution

/-!
# Appendix A.7: products of Fourier–Lebesgue distributions

For every Banach Young triple, convolution gives a periodic tempered product
with the exact constant-one Fourier norm estimate. It agrees with genuine
smooth polynomial multiplication and is independent of exponent representations.
Uniqueness uses polynomial approximation in a finite input exponent; it never
assumes norm density of finite sequences in `ℓ∞`.
-/

noncomputable section
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- The periodic distribution product for an arbitrary admissible Young triple. -/
def youngDistributionProduct (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    𝓢'(ℝ, ℂ) := distributionSynthesis (Coeff.youngConvolution h a b)

@[simp] theorem youngDistributionProduct_coefficientTest (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (n : ℤ) :
    youngDistributionProduct h a b (coefficientTest n) = ∑' k : ℤ, a (n - k) * b k := by
  rw [youngDistributionProduct, distributionSynthesis_coefficientTest, Coeff.youngConvolution_apply]

/-- The output has precisely the claimed Fourier regularity and norm bound. -/
theorem youngDistributionProduct_regular (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    ∃ c : Coeff r, distributionSynthesis c = youngDistributionProduct h a b ∧
      ‖c‖ ≤ ‖a‖ * ‖b‖ :=
  ⟨Coeff.youngConvolution h a b, rfl, Coeff.norm_youngConvolution_le h a b⟩

theorem isPeriodTwoDistribution_youngDistributionProduct (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) : IsPeriodTwoDistribution (youngDistributionProduct h a b) :=
  isPeriodTwoDistribution_distributionSynthesis _

theorem norm_youngDistributionProduct_apply_le (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (g : 𝓢(ℝ, ℂ)) :
    ‖youngDistributionProduct h a b g‖ ≤ (‖a‖ * ‖b‖) * ‖schwartzSamples (𝓕 g)‖ :=
  (norm_distributionSynthesis_apply_le _ g).trans
    (mul_le_mul_of_nonneg_right (Coeff.norm_youngConvolution_le h a b) (norm_nonneg _))

theorem continuous_youngDistributionProduct (h : YoungRelation p q r) :
    Continuous (fun ab : Coeff p × Coeff q => youngDistributionProduct h ab.1 ab.2) :=
  distributionSynthesisCLM.continuous.comp (Coeff.continuous_youngConvolution h)

theorem tendsto_youngDistributionProduct (h : YoungRelation p q r) {ι : Type*} {l : Filter ι}
    {aᵢ : ι → Coeff p} {bᵢ : ι → Coeff q} {a : Coeff p} {b : Coeff q}
    (ha : Filter.Tendsto aᵢ l (nhds a)) (hb : Filter.Tendsto bᵢ l (nhds b)) :
    Filter.Tendsto (fun i => youngDistributionProduct h (aᵢ i) (bᵢ i)) l
      (nhds (youngDistributionProduct h a b)) := by
  simpa only [Function.comp_def] using!
    distributionSynthesisCLM.continuous.tendsto (Coeff.youngConvolution h a b) |>.comp
      (Coeff.tendsto_youngConvolution h ha hb)

theorem youngDistributionProduct_comm (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    youngDistributionProduct h a b = youngDistributionProduct h.symm b a := by
  rw [youngDistributionProduct, Coeff.youngConvolution_comm, youngDistributionProduct]

/-- The product depends only on its two actual distributions, across all admissible exponents. -/
theorem youngDistributionProduct_eq_of_synthesis_eq
    {p' q' r' : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ q')] [Fact (1 ≤ r')]
    (h : YoungRelation p q r) (h' : YoungRelation p' q' r')
    (a : Coeff p) (b : Coeff q) (a' : Coeff p') (b' : Coeff q')
    (ha : distributionSynthesis a = distributionSynthesis a')
    (hb : distributionSynthesis b = distributionSynthesis b') :
    youngDistributionProduct h a b = youngDistributionProduct h' a' b' := by
  apply (distributionSynthesis_eq_iff _ _).mpr
  intro n
  simp only [Coeff.youngConvolution_apply]
  apply tsum_congr
  intro k
  rw [(distributionSynthesis_eq_iff _ _).mp ha, (distributionSynthesis_eq_iff _ _).mp hb]

theorem youngDistributionProduct_eq_distributionProduct (h : YoungRelation p 1 p)
    (a : Coeff p) (b : Coeff 1) : youngDistributionProduct h a b = distributionProduct a b := by
  rw [youngDistributionProduct, Coeff.youngConvolution_eq_convolution, distributionProduct]

/-- Every finite right multiplier agrees with Mathlib's actual smooth multiplication. -/
theorem youngDistributionProduct_truncate_right (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (S : Finset ℤ) :
    youngDistributionProduct h a (Coeff.truncate S b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S b) (distributionSynthesis a) := by
  let b₁ : Coeff 1 := Coeff.ofFinsupp (Coeff.finiteRestriction S b)
  have he : youngDistributionProduct h a (Coeff.truncate S b) =
      distributionProduct a (Coeff.truncate S b₁) := by
    apply (distributionSynthesis_eq_iff _ _).mpr
    intro n
    simp only [Coeff.youngConvolution_apply, Coeff.convolution_apply]
    apply tsum_congr
    intro k
    by_cases hk : k ∈ S <;> simp [b₁, Coeff.truncate_apply, Coeff.ofFinsupp_apply, hk]
  have hpoly : fourierPolynomial S b₁ = fourierPolynomial S b := by
    funext x
    apply Finset.sum_congr rfl
    intro k hk
    simp [b₁, Coeff.ofFinsupp_apply, hk]
  rw [he, distributionProduct_truncate, hpoly]

theorem youngDistributionProduct_truncate_left (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (S : Finset ℤ) :
    youngDistributionProduct h (Coeff.truncate S a) b =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S a) (distributionSynthesis b) := by
  rw [youngDistributionProduct_comm]
  exact youngDistributionProduct_truncate_right h.symm b a S

/-- A finite right exponent gives genuine polynomial-multiplier approximation. -/
theorem tendsto_polynomial_youngDistributionProduct_right (h : YoungRelation p q r) (hq : q ≠ ⊤)
    (a : Coeff p) (b : Coeff q) :
    Filter.Tendsto (fun S : Finset ℤ =>
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S b) (distributionSynthesis a))
      Filter.atTop (nhds (youngDistributionProduct h a b)) := by
  simp_rw [← youngDistributionProduct_truncate_right h]
  exact tendsto_youngDistributionProduct h tendsto_const_nhds (Coeff.tendsto_truncate hq b)

theorem tendsto_polynomial_youngDistributionProduct_left (h : YoungRelation p q r) (hp : p ≠ ⊤)
    (a : Coeff p) (b : Coeff q) :
    Filter.Tendsto (fun S : Finset ℤ =>
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S a) (distributionSynthesis b))
      Filter.atTop (nhds (youngDistributionProduct h a b)) := by
  rw [youngDistributionProduct_comm]
  exact tendsto_polynomial_youngDistributionProduct_right h.symm hp b a

/-- Uniqueness from right polynomial multiplication when the right exponent is finite. -/
theorem youngDistributionProduct_unique_right (h : YoungRelation p q r) (hq : q ≠ ⊤)
    (a : Coeff p) (F : Coeff q → 𝓢'(ℝ, ℂ)) (hF : Continuous F)
    (hpoly : ∀ (b : Coeff q) (S : Finset ℤ), F (Coeff.truncate S b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S b) (distributionSynthesis a)) :
    F = youngDistributionProduct h a := by
  funext b
  have h₁ := (hF.tendsto b).comp (Coeff.tendsto_truncate hq b)
  change Filter.Tendsto (fun S : Finset ℤ => F (Coeff.truncate S b)) Filter.atTop (nhds (F b)) at h₁
  simp_rw [hpoly] at h₁
  exact tendsto_nhds_unique h₁ (tendsto_polynomial_youngDistributionProduct_right h hq a b)

/-- Joint uniqueness covers all endpoints: a Young triple always has a finite input exponent. -/
theorem youngDistributionProduct_unique (h : YoungRelation p q r)
    (F : Coeff p × Coeff q → 𝓢'(ℝ, ℂ)) (hF : Continuous F)
    (hleft : ∀ a b S, F (Coeff.truncate S a, b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S a) (distributionSynthesis b))
    (hright : ∀ a b S, F (a, Coeff.truncate S b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S b) (distributionSynthesis a)) :
    F = fun ab => youngDistributionProduct h ab.1 ab.2 := by
  funext ab
  by_cases hq : q ≠ ⊤
  · exact congrFun (youngDistributionProduct_unique_right h hq ab.1 (fun b => F (ab.1, b))
      (hF.comp (continuous_const.prodMk continuous_id)) (hright ab.1)) ab.2
  · have hp : p ≠ ⊤ := by
      intro hp
      have hh := h
      simp only [YoungRelation, hp, not_not.mp hq, ENNReal.inv_top, add_zero] at hh
      have : (1 : ℝ≥0∞) ≤ 0 := hh ▸ le_self_add
      exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) this
    rw [youngDistributionProduct_comm]
    exact congrFun (youngDistributionProduct_unique_right h.symm hp ab.2 (fun a => F (a, ab.2))
      (hF.comp (continuous_id.prodMk continuous_const)) (fun a S => hleft a ab.2 S)) ab.1

/-- The convolution coefficients characterize the product among all periodic distributions. -/
theorem youngDistributionProduct_eq_of_periodic_coefficients (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (hc : ∀ n, T (coefficientTest n) = ∑' k : ℤ, a (n - k) * b k) :
    youngDistributionProduct h a b = T := by
  apply periodicDistribution_ext (isPeriodTwoDistribution_youngDistributionProduct h a b) hT
  intro n
  rw [youngDistributionProduct_coefficientTest, hc]

/-- A shared Wiener representative gives the previously constructed product. -/
theorem youngDistributionProduct_eq_wiener_product (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (b₁ : Coeff 1)
    (hb : distributionSynthesis b = distributionSynthesis b₁) :
    youngDistributionProduct h a b = distributionProduct a b₁ := by
  have h₁ : YoungRelation p 1 p := by simp [YoungRelation, add_comm]
  rw [youngDistributionProduct_eq_of_synthesis_eq h h₁ a b a b₁ rfl hb,
    youngDistributionProduct_eq_distributionProduct]

/-- Compatibility with actual smooth multiplication holds across exponent representations. -/
theorem youngDistributionProduct_eq_smooth_mul (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (b₁ : Coeff 1)
    (hb : distributionSynthesis b = distributionSynthesis b₁)
    (hg : (fun x : ℝ => continuousSynthesis b₁ (x : AddCircle (2 : ℝ))).HasTemperateGrowth) :
    youngDistributionProduct h a b = TemperedDistribution.smulLeftCLM ℂ
      (fun x : ℝ => continuousSynthesis b₁ (x : AddCircle (2 : ℝ))) (distributionSynthesis a) := by
  rw [youngDistributionProduct_eq_wiener_product h a b b₁ hb]
  exact distributionProduct_eq_smooth_mul a b₁ hg

/-- On shared absolutely summable representatives the product is ordinary function multiplication. -/
theorem youngDistributionProduct_eq_integral (h : YoungRelation p q r)
    (a : Coeff p) (b : Coeff q) (a₁ b₁ : Coeff 1)
    (ha : distributionSynthesis a = distributionSynthesis a₁)
    (hb : distributionSynthesis b = distributionSynthesis b₁) (g : 𝓢(ℝ, ℂ)) :
    youngDistributionProduct h a b g = ∫ x : ℝ,
      continuousSynthesis a₁ (x : AddCircle (2 : ℝ)) *
        (continuousSynthesis b₁ (x : AddCircle (2 : ℝ)) * g x) := by
  have h₁ : YoungRelation 1 1 1 := by simp [YoungRelation]
  rw [youngDistributionProduct_eq_of_synthesis_eq h h₁ a b a₁ b₁ ha hb,
    youngDistributionProduct_eq_distributionProduct]
  exact distributionProduct_eq_integral a₁ b₁ g

end NLS.Fourier
