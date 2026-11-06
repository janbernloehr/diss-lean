import NLS.SequenceSpaces.TotalBoundedTails
import NLS.SequenceSpaces.CompactRowMajorant

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.Coeff



variable {p : ℝ≥0∞} [Fact (1≤p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_outputTail_operator_mono (T : E →L[ℂ] Coeff p)
    (s t : Finset ℤ) (hst : s⊆t) :
    ‖T-(truncateCLM t).comp T‖≤‖T-(truncateCLM s).comp T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖T x-truncate t (T x)‖≤‖T-(truncateCLM s).comp T‖*‖x‖
  exact (norm_sub_truncate_mono s t hst (T x)).trans ((T-(truncateCLM s).comp T).le_opNorm x)

/-- A majorant for all rows outside a fixed finite head bounds every
output truncation that contains that head in operator norm. -/
theorem norm_outputTail_operator_le_of_tailRowMajorant
    (T : E →L[ℂ] Coeff p) (b : Coeff p) (s0 s : Finset ℤ) (hs : s0⊆s)
    (hrow : ∀ m : ℤ, m∉s0 → ∀ x : E, ‖T x m‖≤‖b m‖*‖x‖) :
    ‖T-(truncateCLM s).comp T‖≤‖b-truncate s b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hnorm : ‖T x-truncate s (T x)‖≤‖(‖x‖ : ℂ) • (b-truncate s b)‖ := by
    apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out))
    intro m
    by_cases hm : m∈s
    · simp only [lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_pos hm,sub_self,norm_zero]
      exact norm_nonneg _
    · have hm0 : m∉s0 := fun h => hm (hs h)
      simpa only [lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_neg hm,sub_zero,
        lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x),mul_comm] using hrow m hm0 x
  simpa only [sub_apply,ContinuousLinearMap.comp_apply,truncateCLM_apply,norm_smul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x),mul_comm] using hnorm

theorem exists_uniform_outputTail_operator_of_compact_rowMajorants
    (hp : p≠⊤) {ι : Type*} (T : ι → E →L[ℂ] Coeff p) (b : ι → Coeff p)
    (K : Set (Coeff p)) (hK : IsCompact K) (hb : ∀ i, b i∈K) (s0 : Finset ℤ)
    (hrow : ∀ i m, m∉s0 → ∀ x : E, ‖T i x m‖≤‖b i m‖*‖x‖)
    (ε : ℝ) (hε : 0<ε) :
    ∃ s : Finset ℤ, s0⊆s ∧ ∀ t : Finset ℤ, s⊆t → ∀ i,
      ‖T i-(truncateCLM t).comp (T i)‖<ε := by
  have ht := tendstoUniformlyOn_norm_tail_of_isCompact hp hK
  obtain ⟨s,hs⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp ht) ε hε)
  refine ⟨s0∪s,Finset.subset_union_left,?_⟩
  intro t hst i
  have hbound := norm_outputTail_operator_le_of_tailRowMajorant (T i) (b i) s0 t
    (Finset.Subset.trans Finset.subset_union_left hst) (hrow i)
  apply hbound.trans_lt
  have hh := hs t (Finset.Subset.trans Finset.subset_union_right hst) (b i) (hb i)
  simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hh

end NLS.Coeff
