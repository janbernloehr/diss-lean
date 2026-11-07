import NLS.Articles.KdVEstimates.MainBirkhoffEstimates
import NLS.KdV.HillBirkhoffIntegerLowerNorms
import NLS.SequenceSpaces.ConservedSobolevBootstrap

noncomputable section
set_option autoImplicit false
open NLS.KdV
namespace NLS.Articles.KdVEstimates

theorem exists_original_lowerTarget_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ b : ℝ, 0 < b ∧ ∀ p : RealHillWeightedPotential (hillIntegerWeight m),
      ∀ hmean : p.val.val 0 = 0,
      ‖hillOriginalBirkhoffSobolevRestriction m (m-1) (by omega) p hmean‖ ≤
        b*(1+‖(hillRealNativeIntegerLower m (m-1) (by omega) p).val‖)^(m-1)*
          ‖(hillRealNativeIntegerLower m (m-1) (by omega) p).val‖ := by
  by_cases h1 : m = 1
  · subst m
    refine ⟨1,by norm_num,?_⟩
    intro p hmean
    simpa only [Nat.sub_self,pow_zero,mul_one,one_mul] using
      norm_hillOriginalBirkhoffSobolevRestriction_zero_le 1 p hmean
  · have hj : 1 ≤ m-1 := by omega
    obtain ⟨c,d,hc,_,hbound⟩ := theorem1 (m-1) hj
    refine ⟨2*c,by positivity,?_⟩
    intro p hmean
    let q := hillRealNativeIntegerLower m (m-1) (by omega) p
    have hqmean := hillRealNativeIntegerLower_mean_zero m (m-1) (by omega) p hmean
    let r := hillRealNativeIntegerLower (m-1) (m-1-1) (by omega) q
    have hr : ‖r.val‖ ≤ ‖q.val‖ :=
      WeightedCoeff.norm_inclusionCLM_le _ _ _ q.val
    have hf := (hbound q hqmean).1
    rw [norm_hillOriginalBirkhoffSobolevRestriction_lower m (m-1) (by omega) p hmean]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖r.val‖)
      (add_le_add le_rfl hr) (m-1)
    have hprod := mul_le_mul hpow hr (norm_nonneg _) (by positivity)
    have hlin : ‖q.val‖ ≤ (1+‖q.val‖)^(m-1)*‖q.val‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by linarith [norm_nonneg q.val] : 1 ≤ 1+‖q.val‖) (n := m-1)) (norm_nonneg q.val)
    change ‖hillOriginalBirkhoffSobolevRestriction (m-1) (m-1) le_rfl q hqmean‖ ≤
      c*(‖q.val‖+(1+‖r.val‖)^(m-1)*‖r.val‖) at hf
    have hb := mul_le_mul_of_nonneg_left (add_le_add hlin hprod) hc.le
    exact hf.trans (by convert hb using 1; ring)

/-- The precise dynamical estimate once the actual trajectory is proved to
conserve the two original target norms. This is a conditional intermediate
result, not yet the paper's corollary for all KdV solutions. -/
theorem corollary1_dynamical_of_conserved_target_norms (m : ℕ) (hm : 1 ≤ m) :
    ∃ α : ℝ, 0 < α ∧
      ∀ u : ℝ → RealHillWeightedPotential (hillIntegerWeight m),
      ∀ hmean : ∀ t, (u t).val.val 0 = 0,
      (∀ t, ‖hillOriginalBirkhoffSobolevRestriction m m le_rfl (u t) (hmean t)‖ =
        ‖hillOriginalBirkhoffSobolevRestriction m m le_rfl (u 0) (hmean 0)‖) →
      (∀ t, ‖hillOriginalBirkhoffSobolevRestriction m (m-1) (by omega) (u t) (hmean t)‖ =
        ‖hillOriginalBirkhoffSobolevRestriction m (m-1) (by omega) (u 0) (hmean 0)‖) →
      ∀ t, ‖(u t).val‖ ≤ α*(‖(u 0).val‖+
        (1+‖(hillRealNativeIntegerLower m (m-1) (by omega) (u 0)).val‖)^(m*m+m-1)*
          ‖(hillRealNativeIntegerLower m (m-1) (by omega) (u 0)).val‖) := by
  obtain ⟨c,d,hc,hd,hbound⟩ := theorem1 m hm
  obtain ⟨b,hb,hB⟩ := exists_original_lowerTarget_bound m hm
  refine ⟨d*(c+(1+b)^m*b),by positivity,?_⟩
  intro u hmean hS hT t
  have hf := (hbound (u 0) (hmean 0)).1
  have hi := (hbound (u t) (hmean t)).2
  rw [hS t,hT t] at hi
  exact NLS.SequenceSpaces.conservedSobolev_bootstrap m hm _ _ _ _ _ c d b
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hc.le hd.le hb.le
    hf (hB (u 0) (hmean 0)) hi

theorem original_target_norm_eq_of_actions_eq (M j : ℕ) (hj : j ≤ M)
    (p q : RealHillWeightedPotential (hillIntegerWeight M))
    (hp : p.val.val 0 = 0) (hq : q.val.val 0 = 0)
    (hI : ∀ k, hillOriginalBirkhoffAction (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hp) k =
      hillOriginalBirkhoffAction (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) q hq) k) :
    ‖hillOriginalBirkhoffSobolevRestriction M j hj p hp‖ =
      ‖hillOriginalBirkhoffSobolevRestriction M j hj q hq‖ := by
  apply RealWeightedNatPair.norm_eq_of_pair_sq
  intro k
  have h := hI k
  simp only [hillOriginalBirkhoffAction] at h
  change ((hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hp)).val k).1^2+
      ((hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hp)).val k).2^2 =
    ((hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) q hq)).val k).1^2+
      ((hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) q hq)).val k).2^2
  linarith

/-- The complete printed uniform bound follows from conservation of the
actual physical actions. Conservation for every KdV solution is still a
separate obligation; no such hypothesis is hidden in a solution definition. -/
theorem corollary1_dynamical_of_conserved_actions (m : ℕ) (hm : 1 ≤ m) :
    ∃ α : ℝ, 0 < α ∧
      ∀ u : ℝ → RealHillWeightedPotential (hillIntegerWeight m),
      ∀ hmean : ∀ t, (u t).val.val 0 = 0,
      (∀ t k, hillOriginalBirkhoffAction
          (hillOriginalWeightedMeanZeroSource (hillIntegerWeight m) (u t) (hmean t)) k =
        hillOriginalBirkhoffAction
          (hillOriginalWeightedMeanZeroSource (hillIntegerWeight m) (u 0) (hmean 0)) k) →
      ∀ t, ‖(u t).val‖ ≤ α*(‖(u 0).val‖+
        (1+‖(hillRealNativeIntegerLower m (m-1) (by omega) (u 0)).val‖)^(m*m+m-1)*
          ‖(hillRealNativeIntegerLower m (m-1) (by omega) (u 0)).val‖) := by
  obtain ⟨α,hα,hbound⟩ := corollary1_dynamical_of_conserved_target_norms m hm
  refine ⟨α,hα,?_⟩
  intro u hmean hI
  exact hbound u hmean
    (fun t => original_target_norm_eq_of_actions_eq m m le_rfl (u t) (u 0) (hmean t) (hmean 0) (hI t))
    (fun t => original_target_norm_eq_of_actions_eq m (m-1) (by omega) (u t) (u 0) (hmean t) (hmean 0) (hI t))

end NLS.Articles.KdVEstimates
