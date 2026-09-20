import NLS.ComplexAnalysis.QuadraticProductError
import NLS.SequenceSpaces.DoublingProduct

/-!
# Sequence-space bounds for nonlinear product remainders

A rowwise absolute-sum envelope in the doubled exponent controls the quadratic
remainder in the original exponent. A signed linear sum can then be added
without losing its cancellation.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ComplexAnalysis
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderTriple q p]
variable {ι : Type*}

/-- A doubled-exponent envelope gives a pointwise majorant for the nonlinear product error. -/
theorem norm_product_remainder_le_envelope (u : ℤ → ι → ℂ)
    (hu : ∀ n, Summable (fun i => ‖u n i‖)) (A : Coeff q)
    (hA : ∀ n, (∑' i, ‖u n i‖) ≤ ‖A n‖) (n : ℤ) :
    ‖(∏' i, (1+u n i))-1-∑' i, u n i‖ ≤
      ‖((Real.exp ‖A‖ : ℝ) : ℂ) • Coeff.doublingProduct (p := p) A A n‖ := by
  have hn : (∑' i, ‖u n i‖) ≤ ‖A‖ := (hA n).trans
    (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' A n)
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
    Coeff.doublingProduct_apply, norm_mul]
  apply (norm_tprod_one_add_sub_one_sub_tsum_le (u n) (hu n)).trans
  have hs : (∑' i, ‖u n i‖)^2 ≤ ‖A n‖^2 :=
    pow_le_pow_left₀ (tsum_nonneg (fun _ => norm_nonneg _)) (hA n) 2
  have h := mul_le_mul hs (Real.exp_le_exp.mpr hn) (Real.exp_nonneg _) (sq_nonneg _)
  nlinarith

/-- The nonlinear product remainder is an actual lp coefficient sequence. -/
def productRemainderCoeff (u : ℤ → ι → ℂ) (hu : ∀ n, Summable (fun i => ‖u n i‖))
    (A : Coeff q) (hA : ∀ n, (∑' i, ‖u n i‖) ≤ ‖A n‖) : Coeff p :=
  ⟨fun n => (∏' i, (1+u n i))-1-∑' i, u n i,
    (lp.memℓp (((Real.exp ‖A‖ : ℝ) : ℂ) • Coeff.doublingProduct (p := p) A A)).mono'
      (norm_product_remainder_le_envelope u hu A hA)⟩

/-- The remainder norm is bounded by exp(norm A) times the square of norm A. -/
theorem norm_productRemainderCoeff_le (u : ℤ → ι → ℂ) (hu : ∀ n, Summable (fun i => ‖u n i‖))
    (A : Coeff q) (hA : ∀ n, (∑' i, ‖u n i‖) ≤ ‖A n‖) :
    ‖productRemainderCoeff (p := p) u hu A hA‖ ≤ Real.exp ‖A‖*‖A‖^2 := by
  have h := lp.norm_mono (x := productRemainderCoeff (p := p) u hu A hA)
    (y := ((Real.exp ‖A‖ : ℝ) : ℂ) • Coeff.doublingProduct (p := p) A A)
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' (norm_product_remainder_le_envelope u hu A hA)
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at h
  exact h.trans (by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left
      (Coeff.norm_doublingProduct_le (p := p) A A) (Real.exp_nonneg _))

/-- Adding a signed lp linear sum gives the full product error in the same exponent. -/
theorem memℓp_product_sub_one (u : ℤ → ι → ℂ) (hu : ∀ n, Summable (fun i => ‖u n i‖))
    (A : Coeff q) (hA : ∀ n, (∑' i, ‖u n i‖) ≤ ‖A n‖)
    (L : Coeff p) (hL : ∀ n, ∑' i, u n i = L n) : Memℓp (fun n => (∏' i, (1+u n i))-1) p := by
  have he : (fun n => (∏' i, (1+u n i))-1) = (fun n => (productRemainderCoeff (p := p) u hu A hA+L) n) := by
    funext n
    simp only [lp.coeFn_add, Pi.add_apply, productRemainderCoeff, hL, sub_add_cancel]
  rw [he]
  exact lp.memℓp _

end NLS.ComplexAnalysis
