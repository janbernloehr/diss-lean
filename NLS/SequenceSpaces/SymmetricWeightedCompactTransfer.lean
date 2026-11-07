import NLS.SequenceSpaces.WeightedSchurHilbertBound
import NLS.SequenceSpaces.CompactCoordinateTails
import NLS.SequenceSpaces.CompactOperatorTail

/-! Compactness transfers from a weighted ell1 realization of a symmetric
matrix to its actual bounded Hilbert realization. No uniform lower bound
on the weight, or equivalence of the two Banach topologies, is required. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem isCompactOperator_symmetric_hilbert_of_weighted_one
    (K : Coeff 2 →L[ℂ] Coeff 2) (L : Coeff 1 →L[ℂ] Coeff 1)
    (w : ℤ → ℝ) (hw : ∀ i, 0<w i)
    (hsym : ∀ i j, K (lp.single 2 j 1) i=K (lp.single 2 i 1) j)
    (hentry : ∀ i j, ‖K (lp.single 2 j 1) i‖*w i=‖L (lp.single 1 j 1) i‖*w j)
    (hL : IsCompactOperator L) : IsCompactOperator K := by
  classical
  apply isCompactOperator_of_twoSidedTails
  intro ε hε
  obtain ⟨s,hs⟩ := exists_uniform_single_output_tails_of_compact (by norm_num) L hL (ε/4) (by positivity)
  let T := (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) s).comp
    (K.comp (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) s))
  have hsymT (i j : ℤ) : T (lp.single 2 j 1) i=T (lp.single 2 i 1) j := by
    change ((ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) s).comp
      (K.comp (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) s))) (lp.single 2 j 1) i=_
    rw [twoSidedTail_single_apply,twoSidedTail_single_apply]
    by_cases hi : i∈s <;> by_cases hj : j∈s <;> simp [hi,hj,hsym]
  have hcolT (f : Finset ℤ) (j : ℤ) : (∑ i∈f, ‖T (lp.single 2 j 1) i‖*w i)≤(ε/4)*w j := by
    by_cases hj : j∈s
    · have hz (i : ℤ) : T (lp.single 2 j 1) i=0 := by
        change ((ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) s).comp
          (K.comp (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) s))) (lp.single 2 j 1) i=0
        rw [twoSidedTail_single_apply,if_pos (Or.inr hj)]
      simp only [hz,norm_zero,zero_mul,Finset.sum_const_zero]
      exact mul_nonneg (by positivity) (hw j).le
    · let y := L (lp.single 1 j 1)-truncate s (L (lp.single 1 j 1))
      have he (i : ℤ) : ‖T (lp.single 2 j 1) i‖*w i=‖y i‖*w j := by
        change ‖((ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) s).comp
          (K.comp (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) s))) (lp.single 2 j 1) i‖*w i=
            ‖(L (lp.single 1 j 1)-truncate s (L (lp.single 1 j 1))) i‖*w j
        rw [twoSidedTail_single_apply]
        by_cases hi : i∈s
        · simp [hi,hj]
        · simpa only [hi,hj,or_self,if_false,lp.coeFn_sub,Pi.sub_apply,truncate_apply,sub_zero] using hentry i j
      have hy : (∑ i∈f, ‖y i‖)≤‖y‖ := by
        simpa only [ENNReal.toReal_one,Real.rpow_one] using
          lp.sum_rpow_le_norm_rpow (by norm_num : 0<(1 : ℝ≥0∞).toReal) y f
      calc
        _=(∑ i∈f, ‖y i‖)*w j := by simp_rw [he];rw [Finset.sum_mul]
        _≤‖y‖*w j := mul_le_mul_of_nonneg_right hy (hw j).le
        _≤(ε/4)*w j := mul_le_mul_of_nonneg_right (hs j) (hw j).le
  have hnorm : ‖T‖≤2*(ε/4) :=
    norm_le_two_mul_of_symmetric_weighted_columns T w hw (ε/4) (by positivity) hsymT hcolT
  exact ⟨s,s,hnorm.trans_lt (by linarith)⟩

end NLS.Coeff
