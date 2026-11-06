import NLS.SequenceSpaces.PeriodOneMiuraRealCharts

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

/-- At every complex source there is an analytic shifted Miura chart whose
lift preserves the real form THROUGHOUT its domain. Its positive mass can
be chosen as large as requested. The fixed small-ball injectivity proof
also applies to the conjugate lift, not just at the center. -/
theorem exists_periodOneMiura_energyChart_real_form (q : PeriodOneHminusOne) (A : ℝ) :
    ∃ c : ℝ, 0<c ∧ A<c ∧ ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q∈V ∧
      ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u V ∧
        (∀ a∈V, periodOneMiura (u a)=a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2))) ∧
        ∀ a∈V, IsRealPeriodOneHminusOne a → ∀ k : ℤ, u a (-k)=conj (u a k) := by
  let B : ℝ := ‖q‖
  let R : ℝ := 2*(4*B+1)
  have hR : 0<R := by dsimp [R,B]; positivity
  have hlim : Tendsto (fun m => ‖periodOneMassKernel m‖*R) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_mul] using tendsto_periodOneMassKernel_zero.norm.mul_const R
  obtain ⟨M₁,hM₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/4)))
  obtain ⟨M₂,hM₂⟩ := exists_periodOneMiuraCharts_on_bounded_ball (norm_nonneg q)
  obtain ⟨M₃,hM₃⟩ := exists_nat_gt (2*max A 0+2)
  let m : ℕ := max M₁ (max M₂ M₃)
  have hm₁ : M₁≤m := le_max_left _ _
  have hm₂ : M₂≤m := (le_max_left _ _).trans (le_max_right _ _)
  have hm₃ : M₃≤m := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨v,hv,_,V,hV,hqV,s,hs,hsv,hsolve⟩ := hM₂ m hm₂ q le_rfl
  let W : Set PeriodOneHminusOne := V ∩ s ⁻¹' ball (0 : Coeff 2) R
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hV isOpen_ball
  have hqW : q∈W := by
    refine ⟨hqV,?_⟩
    change s q∈ball (0 : Coeff 2) R
    rw [mem_ball,dist_zero_right,hsv]
    have hh : 4*B+1<R := by dsimp [R,B]; nlinarith [norm_nonneg q]
    exact hv.trans_lt hh
  have hreal (a : PeriodOneHminusOne) (ha : a∈W) (har : IsRealPeriodOneHminusOne a) (k : ℤ) :
      s a (-k)=conj (s a k) := by
    have hconj : periodOneShiftedMiura m (coeffRealConjugation (s a))=a := by
      rw [periodOneShiftedMiura_realConjugation,hsolve a ha.1,periodOne_realConjugation_eq_self a har]
    have hnorm : ‖s a‖≤R := by
      have hh : s a∈ball (0 : Coeff 2) R := ha.2
      exact (by simpa only [mem_ball,dist_zero_right] using hh : ‖s a‖<R).le
    have he := periodOneShiftedMiura_injective_on_ball m R (hM₁ m hm₁).le (s a)
      (coeffRealConjugation (s a)) hnorm (by rw [norm_coeffRealConjugation]; exact hnorm)
      ((hsolve a ha.1).trans hconj.symm)
    have hh := congrArg (fun b : Coeff 2 => b (-k)) he
    simpa only [coeffRealConjugation_apply,neg_neg] using hh
  let c : ℝ := ((m : ℝ)+1)/2
  have hc : 0<c := by dsimp [c]; positivity
  have hAc : A<c := by
    have hmR : (M₃ : ℝ)≤m := by exact_mod_cast hm₃
    dsimp [c]
    linarith [le_max_left A 0]
  let u : PeriodOneHminusOne → Coeff 2 := fun a => s a+lp.single 2 0 (c : ℂ)
  refine ⟨c,hc,hAc,W,hW,hqW,u,?_,?_,?_⟩
  · intro a ha
    exact (hs a ha.1).add analyticAt_const
  · intro a ha
    dsimp only [u]
    have hcC : (c : ℂ)=(((m : ℝ)+1 : ℝ)/2 : ℂ) := by dsimp [c]; push_cast; rfl
    rw [hcC,periodOneMiura_shift,hsolve a ha.1]
  · intro a ha har k
    dsimp only [u]
    by_cases hk : k=0
    · subst k
      simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,neg_zero,if_true,map_add,conj_ofReal]
      exact congrArg (fun z : ℂ => z+(c : ℂ)) (hreal a ha har 0)
    · have hnk : -k≠0 := neg_ne_zero.mpr hk
      simpa only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,if_neg hk,if_neg hnk,
        add_zero,map_add,map_zero] using hreal a ha har k

end NLS
