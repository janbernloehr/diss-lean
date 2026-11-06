import NLS.SequenceSpaces.PeriodOneMiuraRealLift

/-! # Analytic Miura energy charts with a real base lift

The mass may be chosen arbitrarily large. The analytic right inverse
comes from the proved bounded-ball charts; small-ball uniqueness fixes
its base value under real conjugation. Complex nearby inputs retain the
same exact distributional Miura equation and energy translation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

theorem exists_real_periodOneMiura_energyChart (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
        ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u V ∧
          (∀ k : ℤ, u q (-k) = conj (u q k)) ∧
          ∀ a ∈ V, periodOneMiura (u a) =
            a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2)) := by
  let B : ℝ := ‖q‖
  let R : ℝ := 4*B+1
  have hR : 0 < R := by dsimp [R,B]; positivity
  have hlim : Tendsto (fun m => ‖periodOneMassKernel m‖*R) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_mul] using tendsto_periodOneMassKernel_zero.norm.mul_const R
  obtain ⟨M₁,hM₁⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4)))
  obtain ⟨M₂,hM₂⟩ := exists_periodOneMiuraCharts_on_bounded_ball (norm_nonneg q)
  obtain ⟨M₃,hM₃⟩ := exists_nat_gt (2*max A 0+2)
  let m : ℕ := max M₁ (max M₂ M₃)
  have hm₁ : M₁ ≤ m := le_max_left _ _
  have hm₂ : M₂ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm₃ : M₃ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨v,hv,hsolve,V,hV,hqV,s,hs,hsv,hsolveAll⟩ := hM₂ m hm₂ q le_rfl
  have hconj : periodOneShiftedMiura m (coeffRealConjugation v) = q := by
    rw [periodOneShiftedMiura_realConjugation,hsolve,periodOne_realConjugation_eq_self q hq]
  have heq : v = coeffRealConjugation v := periodOneShiftedMiura_injective_on_ball m R
    (hM₁ m hm₁).le v (coeffRealConjugation v) hv (by rw [norm_coeffRealConjugation]; exact hv)
    (hsolve.trans hconj.symm)
  have hvreal (k : ℤ) : v (-k) = conj (v k) := by
    have hh := congrArg (fun a : Coeff 2 => a (-k)) heq
    simpa only [coeffRealConjugation_apply,neg_neg] using hh
  let c : ℝ := ((m : ℝ)+1)/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hAc : A < c := by
    have hmR : (M₃ : ℝ) ≤ m := by exact_mod_cast hm₃
    dsimp [c]
    linarith [le_max_left A 0]
  let u : PeriodOneHminusOne → Coeff 2 := fun a => s a+lp.single 2 0 (c : ℂ)
  refine ⟨c,hc,hAc,V,hV,hqV,u,?_,?_,?_⟩
  · intro a ha
    exact (hs a ha).add analyticAt_const
  · intro k
    dsimp only [u]
    rw [hsv]
    by_cases hk : k = 0
    · subst k
      simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,neg_zero,if_true,map_add,conj_ofReal]
      exact congrArg (fun z : ℂ => z+(c : ℂ)) (hvreal 0)
    · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
      simpa only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,if_neg hk,if_neg hnk,
        add_zero,map_add,map_zero] using hvreal k
  · intro a ha
    dsimp only [u]
    have hcC : (c : ℂ) = (((m : ℝ)+1 : ℝ)/2 : ℂ) := by dsimp [c]; push_cast; rfl
    rw [hcC,periodOneMiura_shift,hsolveAll a ha]

end NLS
