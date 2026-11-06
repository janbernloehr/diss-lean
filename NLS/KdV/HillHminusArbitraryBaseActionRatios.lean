import NLS.KdV.HillHminusArbitraryBasePhysicalActions
import NLS.KdV.HillHminusPhysicalRatioIdentification

/-! # Uniform physical action ratios near any rough source

The common cutoff and complex neighborhood precede all high indices.
Physical recovery holds throughout the rough neighborhood, including at
collapsed gaps and at physical sources of arbitrarily large L2 norm.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem exists_hillHminus_arbitrary_base_high_physical_action_ratios
    (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ R : PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ R V ∧
        (∀ a ∈ V, ‖R a‖ ≤ 2/(n : ℝ) ∧ 0 < (R a).re ∧
          ‖(2*Real.pi*(n : ℝ) : ℂ)*R a-1‖ ≤ 1/2) ∧
        ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ V →
          R (hillOriginalHminusSource p.val) =
            hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) := by
  obtain ⟨r,_hr,_hrpi,hfamily⟩ := exists_hillHminus_arbitrary_base_physical_high_actions q
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily (1/2) (by norm_num)
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,_hK,_hrel,_hmatch,_hJ,_hAa,hFa,hproperties,_hreal,hphysical⟩ := hfamily n hn
  let F := hillHminusNormalizedActionRatio n r K
  let d : ℝ := 2*Real.pi*(n : ℝ)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdc : (d : ℂ) = 2*((Real.pi : ℂ)*(n : ℕ)) := by
    dsimp only [d]
    push_cast
    ring
  let R : PeriodOneHminusOne → ℂ := fun a => F a/(d : ℂ)
  have hRa : AnalyticOnNhd ℂ R V := hFa.div_const
  refine ⟨R,hRa,?_,?_⟩
  · intro a ha
    have hnear := (hproperties a ha).1
    have hFnorm : ‖F a‖ ≤ 2 := by
      have hh := norm_le_norm_sub_add (F a) (1 : ℂ)
      rw [norm_one] at hh
      linarith
    have hFpos : 0 < (F a).re := by
      have hh : 1-(F a).re ≤ ‖F a-1‖ := by
        rw [norm_sub_rev]
        simpa only [sub_re,one_re] using re_le_norm (1-F a)
      linarith
    refine ⟨?_,?_,?_⟩
    · change ‖F a/(d : ℂ)‖ ≤ _
      rw [norm_div,norm_real,Real.norm_of_nonneg hd.le]
      have hnpos : 0 < (n : ℝ) := by positivity
      have hnd : (n : ℝ) ≤ d := by
        have hh := mul_nonneg (show 0 ≤ 2*Real.pi-1 by linarith [Real.pi_gt_three]) hnpos.le
        dsimp only [d]
        nlinarith
      exact (div_le_div_of_nonneg_right hFnorm hd.le).trans
        (div_le_div_of_nonneg_left (by norm_num) hnpos hnd)
    · change 0 < (F a/(d : ℂ)).re
      rw [div_ofReal_re]
      exact div_pos hFpos hd
    · rw [show (2*Real.pi*(n : ℝ) : ℂ) = (d : ℂ) from by
        dsimp only [d]; push_cast; ring]
      change ‖(d : ℂ)*(F a/(d : ℂ))-1‖ ≤ _
      rw [mul_div_cancel₀ _ (ofReal_ne_zero.mpr hd.ne')]
      exact hnear
  · intro p hp
    apply hillHminus_action_ratio_eq_of_physical_action_germ_at p n R (hRa _ hp).continuousAt
    have ht := (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto p
    filter_upwards [ht.eventually (hV.mem_nhds hp)] with v hv
    rw [← (hphysical v hv).1,hillHminusLocalHighAction,(hphysical v hv).2,← hdc]
    change _ = (hillRealGapHalfLength v.val v.property.1 v.property.2 (n : ℕ) : ℂ)^2*
      (F (hillOriginalHminusSource v.val)/(d : ℂ))
    ring

end NLS.KdV
