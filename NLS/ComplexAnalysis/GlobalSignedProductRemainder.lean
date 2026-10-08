import NLS.ComplexAnalysis.SharpExponentialRemainder

/-! # A global signed quadratic product remainder

Comparison with the exponential of the signed sum preserves cancellation
without a logarithm or a smallness hypothesis. The error is controlled by
the sum of squares, rather than the square of the absolute sum.
-/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- Finite products differ from the exponential of their signed sum by a square-sum error. -/
theorem norm_prod_one_add_sub_exp_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ i ∈ s, (1+u i))-Complex.exp (∑ i ∈ s, u i)‖ ≤
      (∑ i ∈ s, ‖u i‖^2)/2*Real.exp (∑ i ∈ s, ‖u i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      Finset.sum_insert ha, Complex.exp_add]
    have he : (1+u a)*(∏ i ∈ s, (1+u i))-Complex.exp (u a)*Complex.exp (∑ i ∈ s, u i) =
        (1+u a)*((∏ i ∈ s, (1+u i))-Complex.exp (∑ i ∈ s, u i))+
        (1+u a-Complex.exp (u a))*Complex.exp (∑ i ∈ s, u i) := by ring
    rw [he]
    have hfactor : ‖1+u a‖ ≤ Real.exp ‖u a‖ :=
      (norm_add_le _ _).trans (by simpa only [norm_one,add_comm] using Real.add_one_le_exp ‖u a‖)
    have hsingle : ‖1+u a-Complex.exp (u a)‖ ≤ ‖u a‖^2/2*Real.exp ‖u a‖ := by
      rw [norm_sub_rev,sub_add_eq_sub_sub]
      exact norm_exp_sub_one_sub_le_half_sq_mul_exp (u a)
    have hexp : ‖Complex.exp (∑ i ∈ s, u i)‖ ≤ Real.exp (∑ i ∈ s, ‖u i‖) :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (norm_sum_le _ _))
    calc
      _ ≤ Real.exp ‖u a‖*((∑ i ∈ s, ‖u i‖^2)/2*Real.exp (∑ i ∈ s, ‖u i‖))+
          (‖u a‖^2/2*Real.exp ‖u a‖)*Real.exp (∑ i ∈ s, ‖u i‖) := by
        apply (norm_add_le _ _).trans
        simp only [norm_mul]
        exact add_le_add (mul_le_mul hfactor ih (norm_nonneg _) (Real.exp_pos _).le)
          (mul_le_mul hsingle hexp (norm_nonneg _) (by positivity))
      _ = _ := by rw [Real.exp_add]; ring

/-- The sum of squared norms converges for every absolutely summable complex family. -/
theorem summable_sq_norm_of_summable_norm {ι : Type*} (u : ι → ℂ)
    (hu : Summable (fun i => ‖u i‖)) : Summable (fun i => ‖u i‖^2) := by
  apply (hu.mul_right (∑' i, ‖u i‖)).of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
  have hi := hu.le_tsum i (fun _ _ => norm_nonneg _)
  nlinarith [norm_nonneg (u i)]

/-- The exponential comparison holds for unconditional infinite products, with no factor restriction. -/
theorem norm_tprod_one_add_sub_exp_tsum_le_global {ι : Type*} (u : ι → ℂ)
    (hu : Summable (fun i => ‖u i‖)) :
    ‖(∏' i, (1+u i))-Complex.exp (∑' i, u i)‖ ≤
      (∑' i, ‖u i‖^2)/2*Real.exp (∑' i, ‖u i‖) := by
  have ht := (multipliable_one_add_of_summable hu).hasProd.sub
    (Complex.continuous_exp.tendsto _ |>.comp hu.of_norm.hasSum)
  have hb := Tendsto.mul (Tendsto.div_const (summable_sq_norm_of_summable_norm u hu).hasSum 2)
    (Real.continuous_exp.tendsto _ |>.comp hu.hasSum)
  exact le_of_tendsto_of_tendsto ht.norm hb
    (Eventually.of_forall (fun s => norm_prod_one_add_sub_exp_sum_le s u))

/-- A global signed quadratic remainder, valid also when numerator factors vanish. -/
theorem norm_tprod_one_add_sub_one_sub_tsum_le_global_signed {ι : Type*} (u : ι → ℂ)
    (hu : Summable (fun i => ‖u i‖)) :
    ‖(∏' i, (1+u i))-1-(∑' i, u i)‖ ≤
      Real.exp (∑' i, ‖u i‖)/2*((‖∑' i, u i‖)^2+∑' i, ‖u i‖^2) := by
  have he : (∏' i, (1+u i))-1-(∑' i, u i) =
      ((∏' i, (1+u i))-Complex.exp (∑' i, u i))+
        (Complex.exp (∑' i, u i)-1-(∑' i, u i)) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hA := norm_tsum_le_tsum_norm hu
  calc
    _ ≤ (∑' i, ‖u i‖^2)/2*Real.exp (∑' i, ‖u i‖)+
        ‖∑' i, u i‖^2/2*Real.exp ‖∑' i, u i‖ :=
      add_le_add (norm_tprod_one_add_sub_exp_tsum_le_global u hu)
        (norm_exp_sub_one_sub_le_half_sq_mul_exp _)
    _ ≤ (∑' i, ‖u i‖^2)/2*Real.exp (∑' i, ‖u i‖)+
        ‖∑' i, u i‖^2/2*Real.exp (∑' i, ‖u i‖) := by gcongr
    _ = _ := by ring

end NLS.ComplexAnalysis
