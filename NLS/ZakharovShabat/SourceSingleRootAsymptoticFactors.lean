import NLS.ZakharovShabat.SourceSingleRootQuotientAnalytic
import NLS.ZakharovShabat.SourceStandardRootProductFactors
import NLS.ComplexAnalysis.SmallAbsoluteProducts

/-!
# Factorization for the asymptotic estimate of Lemma 10.8

The quotient product separates exactly into a midpoint quotient and a
square-root correction. The latter has a linear error bound when its
quadratic radicand perturbation has norm at most one half.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inverse square-root correction is close to one on the closed
half-unit ball. This is the pointwise estimate used in Lemma 10.8. -/
theorem norm_inv_sqrt_one_sub_sub_one_le (q : ℂ) (hq : ‖q‖ ≤ 1/2) :
    ‖(Complex.sqrt (1-q))⁻¹-1‖ ≤ 2*‖q‖ := by
  let s := Complex.sqrt (1-q)
  have hs : s^2 = 1-q := by
    dsimp [s]
    have h := Complex.cpow_nat_inv_pow (1-q) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt, one_div] using h
  have hsq : ‖s‖^2 = ‖1-q‖ := by
    rw [← norm_pow, hs]
  have hlow : (1/2 : ℝ) ≤ ‖1-q‖ := by
    have h : (1:ℝ) ≤ ‖1-q‖+‖q‖ := by
      simpa using (norm_add_le ((1:ℂ)-q) q)
    linarith
  have hsnonneg : 0 ≤ ‖s‖ := norm_nonneg _
  have hslow : (1/2 : ℝ) ≤ ‖s‖ := by nlinarith
  have hs0 : s ≠ 0 := by
    intro he
    have : ‖s‖ = 0 := by rw [he]; simp
    linarith
  have hnum : ‖1-s‖ ≤ ‖q‖ := by
    simpa only [s, norm_sub_rev] using norm_sqrt_one_sub_sub_one_le q
  have heq : s⁻¹-1 = (1-s)/s := by
    field_simp [hs0]
  rw [heq, norm_div]
  have hden : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hslow
  apply (div_le_iff₀ hden).2
  nlinarith [hnum, norm_nonneg q]

/-- A finite product of small inverse square-root corrections is
controlled by the total squared-gap perturbation. -/
theorem norm_prod_inv_sqrt_one_sub_sub_one_le
    {ι : Type*} (s : Finset ι) (q : ι → ℂ)
    (hq : ∀ i ∈ s, ‖q i‖ ≤ 1/2) :
    ‖(∏ i ∈ s, (Complex.sqrt (1-q i))⁻¹)-1‖ ≤
      Real.exp (2*∑ i ∈ s, ‖q i‖)-1 := by
  let u : ι → ℂ := fun i => (Complex.sqrt (1-q i))⁻¹-1
  have hsum : (∑ i ∈ s, ‖u i‖) ≤ 2*∑ i ∈ s, ‖q i‖ := by
    calc
      _ ≤ ∑ i ∈ s, 2*‖q i‖ := Finset.sum_le_sum (fun i hi =>
        norm_inv_sqrt_one_sub_sub_one_le (q i) (hq i hi))
      _ = _ := by rw [Finset.mul_sum]
  have heq : (∏ i ∈ s, (1+u i)) =
      ∏ i ∈ s, (Complex.sqrt (1-q i))⁻¹ := by
    apply Finset.prod_congr rfl
    intro i _
    dsimp [u]
    ring
  rw [← heq]
  exact (s.norm_prod_one_add_sub_one_le u).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

/-- Exact factorization of a single numerator-over-standard-root term.
It is valid even at a zero denominator under totalized field division. -/
theorem singleRootQuotient_factor (σ t g z : ℂ) :
    (σ-z)/normalizedStandardRoot t g z =
      ((σ-z)/(t-z)) * (Complex.sqrt (1-g/(4*(t-z)^2)))⁻¹ := by
  unfold normalizedStandardRoot
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The squared-gap perturbation in the `m`th standard-root factor. -/
def sourceSingleRootGapRadicand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (z : ℂ) : ℂ :=
  (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m)^2 /
    (4*(canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m-z)^2)

/-- The midpoint quotient over the symmetric finite set with one index
removed. -/
def sourceSingleRootMidpointPartialProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (N : ℕ) : ℂ × (Coeff p × CoeffPair p) → ℂ :=
  fun t => ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
    (displacedRoots t.2.1 m-t.1) /
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2.2)
        (periodOnePotential_mem t.2.2) m-t.1)

/-- The corresponding finite product of inverse square-root gap
corrections. -/
def sourceSingleRootGapCorrectionPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (N : ℕ) : ℂ × (Coeff p × CoeffPair p) → ℂ :=
  fun t => ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
    (Complex.sqrt (1-sourceSingleRootGapRadicand hp hp1 t.2.2 m t.1))⁻¹

/-- The literal finite quotient of Corollary 10.6 is exactly the
product of the two terms estimated separately in Lemma 10.8. -/
theorem sourceSingleRootQuotientPartialProduct_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (N : ℕ)
    (t : ℂ × (Coeff p × CoeffPair p)) :
    sourceSingleRootQuotientPartialProduct hp hp1 n N t =
      sourceSingleRootMidpointPartialProduct hp hp1 n N t *
        sourceSingleRootGapCorrectionPartialProduct hp hp1 n N t := by
  unfold sourceSingleRootQuotientPartialProduct
    sourceSingleRootMidpointPartialProduct
    sourceSingleRootGapCorrectionPartialProduct
    sourceSingleRootGapRadicand
  simp_rw [sourceStandardRoot, singleRootQuotient_factor]
  rw [Finset.prod_mul_distrib]

/-- The actual squared-gap correction product obeys the finite error
bound whenever each radicand term is at most one half. -/
theorem norm_sourceSingleRootGapCorrectionPartialProduct_sub_one_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (N : ℕ)
    (t : ℂ × (Coeff p × CoeffPair p))
    (hsmall : ∀ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      ‖sourceSingleRootGapRadicand hp hp1 t.2.2 m t.1‖ ≤ 1/2) :
    ‖sourceSingleRootGapCorrectionPartialProduct hp hp1 n N t-1‖ ≤
      Real.exp (2*∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
        ‖sourceSingleRootGapRadicand hp hp1 t.2.2 m t.1‖)-1 := by
  exact norm_prod_inv_sqrt_one_sub_sub_one_le
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n)
    (sourceSingleRootGapRadicand hp hp1 t.2.2 · t.1) hsmall

/-- The finite quotient differs from its midpoint product by at most
the midpoint product norm times the controlled gap correction. -/
theorem norm_sourceSingleRootQuotientPartialProduct_sub_midpoint_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (N : ℕ)
    (t : ℂ × (Coeff p × CoeffPair p))
    (hsmall : ∀ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      ‖sourceSingleRootGapRadicand hp hp1 t.2.2 m t.1‖ ≤ 1/2) :
    ‖sourceSingleRootQuotientPartialProduct hp hp1 n N t -
      sourceSingleRootMidpointPartialProduct hp hp1 n N t‖ ≤
      ‖sourceSingleRootMidpointPartialProduct hp hp1 n N t‖ *
        (Real.exp (2*∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          ‖sourceSingleRootGapRadicand hp hp1 t.2.2 m t.1‖)-1) := by
  rw [sourceSingleRootQuotientPartialProduct_factor]
  have heq : sourceSingleRootMidpointPartialProduct hp hp1 n N t *
      sourceSingleRootGapCorrectionPartialProduct hp hp1 n N t -
      sourceSingleRootMidpointPartialProduct hp hp1 n N t =
      sourceSingleRootMidpointPartialProduct hp hp1 n N t *
        (sourceSingleRootGapCorrectionPartialProduct hp hp1 n N t-1) := by ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_sourceSingleRootGapCorrectionPartialProduct_sub_one_le
      hp hp1 n N t hsmall) (norm_nonneg _)

end NLS.ZakharovShabat
