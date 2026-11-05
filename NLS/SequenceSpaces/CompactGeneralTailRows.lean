import NLS.SequenceSpaces.CompactRowMajorant

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.Coeff



variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isCompactOperator_of_tailRowMajorant
    (hp : p ≠ ⊤) (T : E →L[ℂ] Coeff p) (b : Coeff p) (s : Finset ℤ)
    (hrow : ∀ (m : ℤ), m ∉ s → ∀ a : E, ‖T a m‖ ≤ ‖b m‖*‖a‖) :
    IsCompactOperator T := by
  let P := truncateCLM (p := p) s
  have hhead : IsCompactOperator (P.comp T) := by
    simpa only [P,ContinuousLinearMap.coe_comp] using
      (isCompactOperator_truncateCLM (p := p) s).comp_clm T
  have htail : IsCompactOperator (T-P.comp T) := by
    apply isCompactOperator_of_rowMajorant hp (T-P.comp T) b
    intro m a
    change ‖(T a-truncate s (T a)) m‖ ≤ ‖b m‖*‖a‖
    rw [lp.coeFn_sub,Pi.sub_apply,truncate_apply]
    by_cases hm : m ∈ s
    · rw [if_pos hm,sub_self,norm_zero]
      positivity
    · rw [if_neg hm,sub_zero]
      exact hrow m hm a
  have h : IsCompactOperator (T-P.comp T+P.comp T : E →L[ℂ] Coeff p) := htail.add hhead
  simpa only [sub_add_cancel] using h

end NLS.Coeff
