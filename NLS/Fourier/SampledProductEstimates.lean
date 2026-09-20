import NLS.Fourier.AbsoluteSampledRows
import NLS.ComplexAnalysis.ProductErrorLp

/-!
# Off-diagonal spectral product errors in lp

For roots k+a(k) and samples n+t(n), with |t(n)| at most one half, the product
of the off-diagonal relative factors differs from one by an lp sequence.
The bound is uniform on input norm balls and over every admissible sampling
sequence. This is the free-reference product estimate needed for D.8–D.9.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩
local instance : (2*p).HolderTriple (2*p) p := holderTriple_double p

/-- The nonlinear remainder of the off-diagonal product, in the original exponent. -/
def sampledProductRemainder (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) : Coeff p :=
  NLS.ComplexAnalysis.productRemainderCoeff (p := p) (perturbedHilbertTerm t a)
    (summable_norm_perturbedHilbertSeries hp1 hp t ht a) (absoluteSampledRowMajorant hp a)
    (tsum_norm_perturbedHilbert_le_majorant hp t ht a)

/-- The full off-diagonal product error as an lp sequence. -/
def sampledProductError (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) : Coeff p :=
  sampledHilbert hp1 hp t ht a+sampledProductRemainder hp1 hp t ht a

/-- The sequence construction gives the unconditional off-diagonal product minus one. -/
theorem sampledProductError_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) (n : ℤ) :
    sampledProductError hp1 hp t ht a n = (∏' k : ℤ, (1+perturbedHilbertTerm t a n k))-1 := by
  change sampledHilbert hp1 hp t ht a n+
    ((∏' k : ℤ, (1+perturbedHilbertTerm t a n k))-1-∑' k : ℤ, perturbedHilbertTerm t a n k) = _
  rw [sampledHilbert_apply]
  ring

/-- The product is exactly the relative product of perturbed roots, with the diagonal omitted. -/
theorem sampledProductError_eq_relative_factors (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) (n : ℤ) :
    sampledProductError hp1 hp t ht a n =
      (∏' k : ℤ, if k = n then 1 else ((k : ℂ)+a k-(n+t n))/((k : ℂ)-(n+t n)))-1 := by
  rw [sampledProductError_apply]
  congr 1
  apply tprod_congr
  intro k
  by_cases hkn : k = n
  · simp [perturbedHilbertTerm, hkn]
  have ha : 1 ≤ ‖(k : ℂ)-n‖ := by
    rw [← Int.cast_sub, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkn)
  have hd : (k : ℂ)-n-t n ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by linarith : 0 < ‖(k : ℂ)-n‖/2)
      (NLS.ComplexAnalysis.norm_sub_ge_half ha (ht n)))
  simp only [perturbedHilbertTerm, if_neg hkn]
  rw [show (k : ℂ)-(n+t n) = (k : ℂ)-n-t n by ring]
  field_simp
  ring

/-- A single bound controls the product error on an input norm ball and all admissible samples. -/
theorem norm_sampledProductError_le (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) {R : ℝ} (ha : ‖a‖ ≤ R) :
    ‖sampledProductError hp1 hp t ht a‖ ≤
      (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*R+
      Real.exp (absoluteSampledRowConstant hp*R)*(absoluteSampledRowConstant hp*R)^2 := by
  have hD := absoluteSampledRowConstant_nonneg hp
  have hA := (norm_absoluteSampledRowMajorant_le hp a).trans (mul_le_mul_of_nonneg_left ha hD)
  have hr := NLS.ComplexAnalysis.norm_productRemainderCoeff_le (p := p) (perturbedHilbertTerm t a)
    (summable_norm_perturbedHilbertSeries hp1 hp t ht a) (absoluteSampledRowMajorant hp a)
    (tsum_norm_perturbedHilbert_le_majorant hp t ht a)
  have hr' : ‖sampledProductRemainder hp1 hp t ht a‖ ≤
      Real.exp (absoluteSampledRowConstant hp*R)*(absoluteSampledRowConstant hp*R)^2 :=
    hr.trans (mul_le_mul (Real.exp_le_exp.mpr hA)
      (pow_le_pow_left₀ (norm_nonneg _) hA 2) (sq_nonneg _) (Real.exp_nonneg _))
  have hL := (norm_sampledHilbert_le hp1 hp t ht a).trans
    (mul_le_mul_of_nonneg_left ha (add_nonneg (hilbertTransformBound_nonneg hp1 hp) (norm_nonneg _)))
  exact (norm_add_le _ _).trans (add_le_add hL hr')

/-- The actual relative off-diagonal products have lp errors for every admissible sampling sequence. -/
theorem memℓp_sampled_relative_product_sub_one (hp1 : 1 < p) (hp : p ≠ ⊤) (t : ℤ → ℂ)
    (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) :
    Memℓp (fun n => (∏' k : ℤ, if k = n then 1 else
      ((k : ℂ)+a k-(n+t n))/((k : ℂ)-(n+t n)))-1) p := by
  have h : Memℓp (fun n => sampledProductError hp1 hp t ht a n) p := lp.memℓp _
  simpa only [sampledProductError_eq_relative_factors] using h

end NLS.Fourier
