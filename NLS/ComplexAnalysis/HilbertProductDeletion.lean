import NLS.ComplexAnalysis.HilbertWeightedProduct
import NLS.SequenceSpaces.DeletedCoordinate

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- Restoring one deleted weight restores exactly its original factor. -/
theorem hilbertWeightedProduct_eq_factor_mul_deleted (b a : Coeff 2) (n : ℤ) :
    hilbertWeightedProduct b a=(1+a n*b n)*hilbertWeightedProduct (Coeff.deleteCoordinate n b) a := by
  let h : ℤ → ℂ := fun m => if m=n then 1+a n*b n else 1
  have hh : Multipliable h := (hasProd_ite_eq n (1+a n*b n)).multipliable
  have he (m : ℤ) : 1+a m*b m=h m*(1+a m*Coeff.deleteCoordinate n b m) := by
    by_cases hm : m=n
    · subst m
      simp only [h,if_true,Coeff.deleteCoordinate_apply_same,mul_zero,add_zero,mul_one]
    · rw [Coeff.deleteCoordinate_apply_other n m hm]
      simp only [h,if_neg hm,one_mul]
  unfold hilbertWeightedProduct
  simp_rw [he]
  rw [hh.tprod_mul (multipliable_hilbertWeightedFactors (Coeff.deleteCoordinate n b) a)]
  rw [show (∏' m : ℤ, h m)=1+a n*b n from tprod_ite_eq n (fun _ : ℤ => 1+a n*b n)]
  simp only [h,if_true,Coeff.deleteCoordinate_apply_same,mul_zero,add_zero,mul_one]

/-- Deleting one weight changes an entire Hilbert product by a bound
linear in that weight, uniformly on each bounded input ball. -/
theorem norm_hilbertWeightedProduct_deleted_sub_le (b a : Coeff 2) (n : ℤ) :
    ‖hilbertWeightedProduct (Coeff.deleteCoordinate n b) a-hilbertWeightedProduct b a‖≤
      ‖a‖*‖b n‖*Real.exp (‖a‖*‖b‖) := by
  have hdel : ‖Coeff.deleteCoordinate n b‖≤‖b‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0)
    intro m
    by_cases hm : m=n
    · subst m
      rw [Coeff.deleteCoordinate_apply_same,norm_zero]
      exact norm_nonneg _
    · rw [Coeff.deleteCoordinate_apply_other n m hm]
  have hprod : ‖hilbertWeightedProduct (Coeff.deleteCoordinate n b) a‖≤Real.exp (‖a‖*‖b‖) :=
    (norm_hilbertWeightedProduct_le _ _).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdel (norm_nonneg a)))
  rw [hilbertWeightedProduct_eq_factor_mul_deleted b a n]
  rw [show hilbertWeightedProduct (Coeff.deleteCoordinate n b) a-
      (1+a n*b n)*hilbertWeightedProduct (Coeff.deleteCoordinate n b) a=
      -(a n*b n)*hilbertWeightedProduct (Coeff.deleteCoordinate n b) a by ring]
  rw [norm_mul,norm_neg,norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_right
    (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) a n) (norm_nonneg _)) hprod
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end NLS.ComplexAnalysis
