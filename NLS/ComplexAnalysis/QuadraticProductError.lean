import NLS.ComplexAnalysis.SmallAbsoluteProducts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A quadratic product error after retaining the linear sum

The first-order term is a signed complex sum. Only the remainder is estimated
by absolute values, preserving the cancellation needed in sampled lp estimates.
Factors may vanish; no logarithm or division by a factor is used.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- The finite product remainder is bounded by the corresponding exponential remainder. -/
theorem norm_prod_one_add_sub_one_sub_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ i ∈ s, (1+u i))-1-∑ i ∈ s, u i‖ ≤
      Real.exp (∑ i ∈ s, ‖u i‖)-1-∑ i ∈ s, ‖u i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    rw [show (1+u a)*(∏ i ∈ s, (1+u i))-1-(u a+∑ i ∈ s, u i) =
      ((∏ i ∈ s, (1+u i))-1-∑ i ∈ s, u i)+u a*((∏ i ∈ s, (1+u i))-1) by ring]
    calc
      _ ≤ (Real.exp (∑ i ∈ s, ‖u i‖)-1-∑ i ∈ s, ‖u i‖)+
          ‖u a‖*(Real.exp (∑ i ∈ s, ‖u i‖)-1) := by
        apply (norm_add_le _ _).trans
        rw [norm_mul]
        exact add_le_add ih (mul_le_mul_of_nonneg_left (s.norm_prod_one_add_sub_one_le u) (norm_nonneg _))
      _ ≤ _ := by
        rw [Real.exp_add]
        have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp ‖u a‖)
          (Real.exp_nonneg (∑ i ∈ s, ‖u i‖))
        nlinarith

/-- The real exponential remainder is quadratic, with an exponential bound at any nonnegative argument. -/
theorem exp_sub_one_sub_le_sq_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x-1-x ≤ x^2*Real.exp x := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  have he : Complex.exp (x : ℂ)-(∑ m ∈ Finset.range 2, (x : ℂ)^m/(m.factorial : ℂ)) =
      ((Real.exp x-1-x : ℝ) : ℂ) := by
    simp [Finset.sum_range_succ, Complex.ofReal_exp]
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at h
  exact (le_abs_self _).trans h

/-- Absolutely summable perturbations have a quadratically controlled infinite-product remainder. -/
theorem norm_tprod_one_add_sub_one_sub_tsum_le {ι : Type*} (u : ι → ℂ)
    (hu : Summable (fun i => ‖u i‖)) :
    ‖(∏' i, (1+u i))-1-∑' i, u i‖ ≤ (∑' i, ‖u i‖)^2*Real.exp (∑' i, ‖u i‖) := by
  have ht := ((multipliable_one_add_of_summable hu).hasProd.sub_const 1).sub hu.of_norm.hasSum
  have hb : ∀ s : Finset ι, ‖(∏ i ∈ s, (1+u i))-1-∑ i ∈ s, u i‖ ≤
      (∑ i ∈ s, ‖u i‖)^2*Real.exp (∑ i ∈ s, ‖u i‖) := fun s =>
    (norm_prod_one_add_sub_one_sub_sum_le s u).trans
      (exp_sub_one_sub_le_sq_mul_exp (Finset.sum_nonneg (fun i _ => norm_nonneg (u i))))
  exact le_of_tendsto_of_tendsto ht.norm (hu.hasSum.pow 2 |>.mul (Real.continuous_exp.tendsto _ |>.comp hu.hasSum))
    (Eventually.of_forall hb)

/-- A bounded absolute sum controls the nonlinear error, retaining the signed linear contribution. -/
theorem norm_tprod_one_add_sub_one_le_linear_add_square {ι : Type*} (u : ι → ℂ)
    (hu : Summable (fun i => ‖u i‖)) {B : ℝ} (hB : (∑' i, ‖u i‖) ≤ B) :
    ‖(∏' i, (1+u i))-1‖ ≤ ‖∑' i, u i‖+Real.exp B*(∑' i, ‖u i‖)^2 := by
  have h := norm_le_norm_sub_add ((∏' i, (1+u i))-1) (∑' i, u i)
  have hr := (norm_tprod_one_add_sub_one_sub_tsum_le u hu).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hB) (sq_nonneg _))
  nlinarith

end NLS.ComplexAnalysis
