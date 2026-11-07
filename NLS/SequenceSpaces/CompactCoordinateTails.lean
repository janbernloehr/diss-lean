import NLS.SequenceSpaces.TotalBoundedTails

/-! Compact operators have uniformly small Fourier output tails on all
unit coordinate vectors, with ONE finite set before every input label. -/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem exists_uniform_single_output_tails_of_compact (hp : p≠⊤)
    (T : Coeff p →L[ℂ] Coeff p) (hT : IsCompactOperator T)
    (ε : ℝ) (hε : 0<ε) :
    ∃ s : Finset ℤ, ∀ j : ℤ, ‖T (lp.single p j 1)-truncate s (T (lp.single p j 1))‖≤ε := by
  let K := closure (T '' closedBall (0 : Coeff p) 1)
  have hK : IsCompact K := hT.isCompact_closure_image_of_bounded isBounded_closedBall
  obtain ⟨s,hs⟩ := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_norm_tail_of_isCompact hp hK) ε hε).exists
  refine ⟨s,?_⟩
  intro j
  have hj : T (lp.single p j 1)∈K := by
    apply subset_closure
    refine ⟨lp.single p j 1,?_,rfl⟩
    rw [mem_closedBall_zero_iff,lp.norm_single (zero_lt_one.trans_le (Fact.out : 1≤p))]
    norm_num
  have hh := hs _ hj
  simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hh.le

theorem complement_truncate_single (s : Finset ℤ) (j : ℤ) :
    (ContinuousLinearMap.id ℂ (Coeff p)-truncateCLM (p := p) s) (lp.single p j 1)=
      if j∈s then 0 else lp.single p j 1 := by
  classical
  ext i
  by_cases hj : j∈s
  · simp only [if_pos hj,sub_apply,ContinuousLinearMap.id_apply,truncateCLM_apply,
      lp.coeFn_sub,Pi.sub_apply,lp.coeFn_zero,Pi.zero_apply,truncate_apply]
    by_cases hi : i=j
    · subst i
      simp [hj]
    · simp [lp.single_apply,hi]
  · simp only [if_neg hj,sub_apply,ContinuousLinearMap.id_apply,truncateCLM_apply,
      lp.coeFn_sub,Pi.sub_apply,truncate_apply]
    by_cases hi : i∈s
    · have hij : i≠j := fun h => hj (h ▸ hi)
      simp [hi,lp.single_apply,hij]
    · simp [hi]

theorem twoSidedTail_single_apply (T : Coeff p →L[ℂ] Coeff p) (s : Finset ℤ) (i j : ℤ) :
    ((ContinuousLinearMap.id ℂ (Coeff p)-truncateCLM (p := p) s).comp
      (T.comp (ContinuousLinearMap.id ℂ (Coeff p)-truncateCLM (p := p) s))) (lp.single p j 1) i=
        if i∈s ∨ j∈s then 0 else T (lp.single p j 1) i := by
  classical
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,complement_truncate_single]
  by_cases hj : j∈s
  · simp [hj]
  · simp only [if_neg hj,sub_apply,ContinuousLinearMap.id_apply,truncateCLM_apply,
      lp.coeFn_sub,Pi.sub_apply,truncate_apply]
    by_cases hi : i∈s <;> simp [hi,hj]

end NLS.Coeff
