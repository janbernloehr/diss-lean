import NLS.SequenceSpaces.PeriodOneMiuraRealCharts

/-! # Miura energy charts preserving the real form on a neighborhood

Strict smallness of the massive inverse leaves room to enlarge the
uniqueness ball. Continuity of the analytic right inverse then puts every
nearby solution in that ball. Real inputs are fixed by conjugation by
uniqueness, throughout one complex open source neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

theorem periodOneShiftedMiura_real_of_small_solution (m : ℕ) (R : ℝ)
    (hsmall : ‖periodOneMassKernel m‖*R ≤ 1/4)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (v : Coeff 2) (hv : ‖v‖ ≤ R) (hsolve : periodOneShiftedMiura m v = q) :
    ∀ k : ℤ, v (-k) = conj (v k) := by
  have hconj : periodOneShiftedMiura m (coeffRealConjugation v) = q := by
    rw [periodOneShiftedMiura_realConjugation,hsolve,periodOne_realConjugation_eq_self q hq]
  have heq : v = coeffRealConjugation v := periodOneShiftedMiura_injective_on_ball m R
    hsmall v (coeffRealConjugation v) hv (by rw [norm_coeffRealConjugation]; exact hv)
    (hsolve.trans hconj.symm)
  intro k
  have hh := congrArg (fun a : Coeff 2 => a (-k)) heq
  simpa only [coeffRealConjugation_apply,neg_neg] using hh

theorem exists_real_preserving_periodOneMiura_energyChart (q : PeriodOneHminusOne)
    (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
        ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u V ∧
          (∀ a ∈ V, IsRealPeriodOneHminusOne a →
            ∀ k : ℤ, u a (-k) = conj (u a k)) ∧
          ∀ a ∈ V, periodOneMiura (u a) =
            a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2)) := by
  let B : ℝ := ‖q‖
  let R : ℝ := 4*B+1
  have hR : 0 < R := by dsimp [R,B]; positivity
  have hlim : Tendsto (fun m => ‖periodOneMassKernel m‖*(2*R)) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_mul] using
      tendsto_periodOneMassKernel_zero.norm.mul_const (2*R)
  obtain ⟨M₁,hM₁⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4)))
  obtain ⟨M₂,hM₂⟩ := exists_periodOneMiuraCharts_on_bounded_ball (norm_nonneg q)
  obtain ⟨M₃,hM₃⟩ := exists_nat_gt (2*max A 0+2)
  let m : ℕ := max M₁ (max M₂ M₃)
  have hm₁ : M₁ ≤ m := le_max_left _ _
  have hm₂ : M₂ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm₃ : M₃ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨v,hv,_,U,hU,hqU,s,hs,hsv,hsolve⟩ := hM₂ m hm₂ q le_rfl
  let V : Set PeriodOneHminusOne := U ∩ s ⁻¹' ball 0 (2*R)
  have hV : IsOpen V := hs.continuousOn.isOpen_inter_preimage hU isOpen_ball
  have hqV : q ∈ V := by
    refine ⟨hqU,?_⟩
    rw [mem_preimage,mem_ball,dist_zero_right,hsv]
    exact hv.trans_lt (by linarith)
  let c : ℝ := ((m : ℝ)+1)/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hAc : A < c := by
    have hmR : (M₃ : ℝ) ≤ m := by exact_mod_cast hm₃
    dsimp [c]
    linarith [le_max_left A 0]
  let u : PeriodOneHminusOne → Coeff 2 := fun a => s a+lp.single 2 0 (c : ℂ)
  refine ⟨c,hc,hAc,V,hV,hqV,u,?_,?_,?_⟩
  · intro a ha
    exact (hs a ha.1).add analyticAt_const
  · intro a ha hreal k
    have hsa : ‖s a‖ ≤ 2*R := (mem_ball_zero_iff.mp ha.2).le
    have hsreal := periodOneShiftedMiura_real_of_small_solution m (2*R)
      (hM₁ m hm₁).le a hreal (s a) hsa (hsolve a ha.1)
    dsimp only [u]
    by_cases hk : k = 0
    · subst k
      simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,neg_zero,
        if_true,map_add,conj_ofReal]
      exact congrArg (fun z : ℂ => z+(c : ℂ)) (hsreal 0)
    · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
      simpa only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,if_neg hk,
        if_neg hnk,add_zero,map_add,map_zero] using hsreal k
  · intro a ha
    dsimp only [u]
    have hcC : (c : ℂ) = (((m : ℝ)+1 : ℝ)/2 : ℂ) := by dsimp [c]; push_cast; rfl
    rw [hcC,periodOneMiura_shift,hsolve a ha.1]

end NLS
