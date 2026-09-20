import NLS.Fourier.SampledProductEstimates

/-!
# A common lp majorant on every sampling disc

The majorant depends only on the root displacement, not on any choice of
samples. Thus one coefficient controls every point of its closed half-unit
disc at once, as needed for subsequent Cauchy estimates.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩
local instance : (2*p).HolderTriple (2*p) p := holderTriple_double p

/-- A positive majorant for the linear term and the quadratic product remainder. -/
def sampledProductMajorant (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) : Coeff p :=
  Coeff.magnitude (hilbertTransform hp1 hp a)+Coeff.magnitude (hilbertSquareMajorant a)+
    (Real.exp ‖absoluteSampledRowMajorant hp a‖ : ℂ) •
      Coeff.magnitude (Coeff.doublingProduct (p := p)
        (absoluteSampledRowMajorant hp a) (absoluteSampledRowMajorant hp a))

/-- Its coefficients are nonnegative real numbers with an explicit three-term formula. -/
theorem sampledProductMajorant_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    sampledProductMajorant hp1 hp a n =
      (‖hilbertTransform hp1 hp a n‖+‖hilbertSquareMajorant a n‖+
        Real.exp ‖absoluteSampledRowMajorant hp a‖*‖absoluteSampledRowMajorant hp a n‖^2 : ℝ) := by
  simp only [sampledProductMajorant, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, Coeff.magnitude_apply, Coeff.doublingProduct_apply,
    norm_mul, pow_two, Complex.ofReal_add, Complex.ofReal_mul]

/-- No cancellation occurs inside the positive majorant. -/
theorem norm_sampledProductMajorant_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    ‖sampledProductMajorant hp1 hp a n‖ =
      ‖hilbertTransform hp1 hp a n‖+‖hilbertSquareMajorant a n‖+
        Real.exp ‖absoluteSampledRowMajorant hp a‖*‖absoluteSampledRowMajorant hp a n‖^2 := by
  rw [sampledProductMajorant_apply, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- One coefficient bounds every admissible choice of the sampled product error. -/
theorem norm_sampledProductError_apply_le_majorant (hp1 : 1 < p) (hp : p ≠ ⊤)
    (t : ℤ → ℂ) (ht : ∀ n, ‖t n‖ ≤ (1 : ℝ)/2) (a : Coeff p) (n : ℤ) :
    ‖sampledProductError hp1 hp t ht a n‖ ≤ ‖sampledProductMajorant hp1 hp a n‖ := by
  rw [norm_sampledProductMajorant_apply]
  have hL : ‖sampledHilbert hp1 hp t ht a n‖ ≤
      ‖hilbertTransform hp1 hp a n‖+‖hilbertSquareMajorant a n‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl (norm_tsum_perturbedHilbert_correction_le t ht a n))
  have hR := NLS.ComplexAnalysis.norm_product_remainder_le_envelope (p := p)
    (perturbedHilbertTerm t a) (summable_norm_perturbedHilbertSeries hp1 hp t ht a)
    (absoluteSampledRowMajorant hp a) (tsum_norm_perturbedHilbert_le_majorant hp t ht a) n
  simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
    Coeff.doublingProduct_apply, ← pow_two, norm_pow] at hR
  exact (norm_add_le _ _).trans (add_le_add hL hR)

/-- The common majorant has the same norm-ball bound as each individual sampled error. -/
theorem norm_sampledProductMajorant_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) {R : ℝ} (ha : ‖a‖ ≤ R) :
    ‖sampledProductMajorant hp1 hp a‖ ≤
      (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*R+
      Real.exp (absoluteSampledRowConstant hp*R)*(absoluteSampledRowConstant hp*R)^2 := by
  have hA := (norm_absoluteSampledRowMajorant_le hp a).trans
    (mul_le_mul_of_nonneg_left ha (absoluteSampledRowConstant_nonneg hp))
  have hL : ‖Coeff.magnitude (hilbertTransform hp1 hp a)+Coeff.magnitude (hilbertSquareMajorant a)‖ ≤
      (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*R := by
    apply (norm_add_le _ _).trans
    simp only [Coeff.norm_magnitude]
    calc
      _ ≤ hilbertTransformBound hp1 hp*‖a‖+‖a‖*‖hilbertSquareCoeffs‖ :=
        add_le_add (norm_hilbertTransform_apply_le hp1 hp a) (norm_hilbertSquareMajorant_le a)
      _ = (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*‖a‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha
        (add_nonneg (hilbertTransformBound_nonneg hp1 hp) (norm_nonneg _))
  apply (norm_add_le _ _).trans
  apply add_le_add hL
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), Coeff.norm_magnitude]
  apply (mul_le_mul_of_nonneg_left (Coeff.norm_doublingProduct_le (p := p) _ _)
    (Real.exp_nonneg _)).trans
  rw [← pow_two]
  exact mul_le_mul (Real.exp_le_exp.mpr hA) (pow_le_pow_left₀ (norm_nonneg _) hA 2)
    (sq_nonneg _) (Real.exp_nonneg _)

/-- The estimate holds throughout each disc, with no sampling sequence in the majorant. -/
theorem norm_relative_product_sub_one_le_majorant (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) (t : ℂ) (ht : ‖t‖ ≤ (1 : ℝ)/2) :
    ‖(∏' k : ℤ, if k = n then 1 else ((k : ℂ)+a k-(n+t))/((k : ℂ)-(n+t)))-1‖ ≤
      ‖sampledProductMajorant hp1 hp a n‖ := by
  simpa only [sampledProductError_eq_relative_factors] using
    norm_sampledProductError_apply_le_majorant hp1 hp (fun _ => t) (fun _ => ht) a n

end NLS.Fourier
