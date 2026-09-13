import NLS.SequenceSpaces.ConvolutionRows

/-!
# Iterated convolution rows

The two reciprocal denominators in Lemma 6.8(ii) lead to a nested row norm.
Two applications of powered Young construct its outer sequence. All rows
are actual `lp` elements, so their defining power sums converge.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p r q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] [Fact (1 ≤ q)]

/-- The norm of an individual convolution row has a uniform product bound. -/
theorem norm_convolutionRow_le (a : Coeff p) (b : Coeff r) (m : ℤ) :
    ‖convolutionRow a b m‖ ≤ ‖a‖ * ‖b‖ := by
  apply (norm_multiplier_le _ _).trans
  rw [norm_reindex]
  exact mul_le_mul_of_nonneg_right (norm_exponentInclusion_le le_top a) (norm_nonneg _)

/-- All row norms, as a bounded nonnegative complex sequence. -/
def convolutionRowNormBounded (a : Coeff p) (b : Coeff r) : Coeff ⊤ :=
  ⟨fun m => (‖convolutionRow a b m‖ : ℂ), memℓp_infty ⟨‖a‖*‖b‖, by
    rintro _ ⟨m,rfl⟩
    simpa using norm_convolutionRow_le a b m⟩⟩

@[simp] theorem convolutionRowNormBounded_apply (a : Coeff p) (b : Coeff r) (m : ℤ) :
    convolutionRowNormBounded a b m = (‖convolutionRow a b m‖ : ℂ) := rfl

/-- The outer row, after taking the inner row norm. -/
def iteratedConvolutionRow (a : Coeff p) (b c : Coeff r) (m : ℤ) : Coeff r :=
  convolutionRow (convolutionRowNormBounded a c) b m

@[simp] theorem iteratedConvolutionRow_apply (a : Coeff p) (b c : Coeff r) (m j : ℤ) :
    iteratedConvolutionRow a b c m j = (‖convolutionRow a c (m-j)‖ : ℂ) * b j := rfl

/-- The nested row norm is uniformly bounded by the product of all three norms. -/
theorem norm_iteratedConvolutionRow_le (a : Coeff p) (b c : Coeff r) (m : ℤ) :
    ‖iteratedConvolutionRow a b c m‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  have h : ‖iteratedConvolutionRow a b c m‖ ≤ ‖(‖a‖*‖c‖ : ℂ) • b‖ := by
    apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ r)).ne'
    intro j
    simp only [iteratedConvolutionRow_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), lp.coeFn_smul, Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_convolutionRow_le a c (m-j)) (norm_nonneg _)
  calc
    _ ≤ ‖(‖a‖*‖c‖ : ℂ) • b‖ := h
    _ = _ := by simp only [norm_smul, norm_mul, Complex.norm_real, norm_norm]; ring

/-- Increasing both inner exponents contracts the entire nested row norm. -/
theorem norm_iteratedConvolutionRow_exponent_le (hrq : r ≤ q)
    (a : Coeff p) (b c : Coeff r) (m : ℤ) :
    ‖iteratedConvolutionRow a (exponentInclusion hrq b) (exponentInclusion hrq c) m‖ ≤
      ‖iteratedConvolutionRow a b c m‖ := by
  apply le_trans _ (norm_exponentInclusion_le hrq (iteratedConvolutionRow a b c m))
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
  intro j
  simp only [iteratedConvolutionRow_apply, exponentInclusion_apply, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (norm_convolutionRow_exponent_le hrq a c (m-j)) (norm_nonneg _)

/-- Two powered Young estimates construct the exact outer sequence of nested row norms. -/
theorem exists_iteratedConvolutionRowNorm (hp : p ≠ ⊤) (hrp : r ≤ p)
    (a : Coeff p) (b c : Coeff r) :
    ∃ d : Coeff p, (∀ m : ℤ, d m = (‖iteratedConvolutionRow a b c m‖ : ℂ)) ∧
      ‖d‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  obtain ⟨e, he, hen⟩ := exists_convolutionRowNorm hp hrp a c
  obtain ⟨d, hd, hdn⟩ := exists_convolutionRowNorm hp hrp e b
  have hrow (m : ℤ) : convolutionRow e b m = iteratedConvolutionRow a b c m := by
    ext j
    simp only [convolutionRow_apply, iteratedConvolutionRow_apply, he]
  refine ⟨d, fun m => by rw [hd, hrow], ?_⟩
  exact hdn.trans ((mul_le_mul_of_nonneg_right hen (norm_nonneg b)).trans_eq (by ring))

/-- Sampling at twice the signed output frequency preserves the outer estimate. -/
theorem exists_evenIteratedConvolutionRowNorm (hp : p ≠ ⊤) (hrp : r ≤ p)
    (a : Coeff p) (b c : Coeff r) :
    ∃ d : Coeff p, (∀ n : ℤ, d n = (‖iteratedConvolutionRow a b c (2*n)‖ : ℂ)) ∧
      ‖d‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  obtain ⟨d, hd, hn⟩ := exists_iteratedConvolutionRowNorm hp hrp a b c
  exact ⟨periodHalve d, fun n => hd (2*n), (norm_periodHalve_le d).trans hn⟩

end NLS.Coeff
