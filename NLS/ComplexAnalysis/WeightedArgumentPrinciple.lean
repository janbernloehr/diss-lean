import NLS.ComplexAnalysis.ArgumentPrinciple

/-! The argument principle with an analytic weight, including multiple zeros. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Complex
open scoped Classical
namespace NLS.ComplexAnalysis

/-- An analytic weight evaluates each logarithmic principal part at its pole. -/
theorem circleIntegral_weighted_logDerivPrincipalParts
    (f : ℂ → ℂ) (s : Finset ℂ) {q : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hq : AnalyticOnNhd ℂ q (closedBall c R))
    (hs : (s : Set ℂ) ⊆ ball c R) :
    (∮ z in C(c,R), q z * logDerivPrincipalParts f s z) =
      (2*Real.pi*I) * ∑ a ∈ s, (analyticOrderNatAt f a : ℂ) * q a := by
  have hi : ∀ a ∈ s, CircleIntegrable
      (fun z : ℂ => (analyticOrderNatAt f a : ℂ) * (q z/(z-a))) c R := by
    intro a ha
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (analyticAt_const.mul ((hq z (sphere_subset_closedBall hz)).div
      (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz (hs ha))))).continuousAt.continuousWithinAt
  calc
    _ = ∮ z in C(c,R), ∑ a ∈ s, (analyticOrderNatAt f a : ℂ) * (q z/(z-a)) := by
      congr 1
      funext z
      simp only [logDerivPrincipalParts,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = ∑ a ∈ s, ∮ z in C(c,R), (analyticOrderNatAt f a : ℂ) * (q z/(z-a)) :=
      circleIntegral.integral_fun_sum hi
    _ = (2*Real.pi*I) * ∑ a ∈ s, (analyticOrderNatAt f a : ℂ) * q a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [circleIntegral.integral_const_mul]
      have hC : (∮ z in C(c,R), q z/(z-a)) = (2*Real.pi*I)*q a := by
        simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
          hq.differentiableOn.circleIntegral_sub_inv_smul (hs ha)
      rw [hC]
      ring

/-- Weighted argument principle on a closed disc. The finite set may also
contain nonzeros, whose analytic orders contribute zero. -/
theorem circleIntegral_weighted_logDeriv_eq_sum
    {f q : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hq : AnalyticOnNhd ℂ q (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0)
    (hfinite : ∀ z ∈ closedBall c R, analyticOrderAt f z ≠ ⊤)
    (s : Finset ℂ) (hs : (s : Set ℂ) ⊆ ball c R)
    (hcover : ∀ z ∈ closedBall c R, f z = 0 → z ∈ s) :
    (∮ z in C(c,R), q z * logDeriv f z) =
      (2*Real.pi*I) * ∑ a ∈ s, (analyticOrderNatAt f a : ℂ) * q a := by
  let g := toMeromorphicNFOn
    (fun z => logDeriv f z-logDerivPrincipalParts f s z) (closedBall c R)
  have hg : AnalyticOnNhd ℂ g (closedBall c R) :=
    analyticOnNhd_logDeriv_remainder hf hfinite s hcover
  have hqg : AnalyticOnNhd ℂ (fun z => q z*g z) (closedBall c R) := hq.mul hg
  have hzs : ∀ z ∈ sphere c R, z ∉ s := fun z hz hmem => (ne_of_lt (hs hmem)) hz
  have hgi : CircleIntegrable (fun z => q z*g z) c R :=
    (hqg.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hpi : CircleIntegrable (fun z => q z*logDerivPrincipalParts f s z) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact ((hq z (sphere_subset_closedBall hz)).mul
      (analyticAt_logDerivPrincipalParts f s (hzs z hz))).continuousAt.continuousWithinAt
  calc
    _ = ∮ z in C(c,R), q z*g z+q z*logDerivPrincipalParts f s z := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have he : g z = logDeriv f z-logDerivPrincipalParts f s z :=
        logDeriv_remainder_normalForm_eq hf s (sphere_subset_closedBall hz) (hzs z hz) (hb z hz)
      dsimp only
      rw [he]
      ring
    _ = (∮ z in C(c,R), q z*g z)+∮ z in C(c,R), q z*logDerivPrincipalParts f s z :=
      circleIntegral.integral_add hgi hpi
    _ = (2*Real.pi*I) * ∑ a ∈ s, (analyticOrderNatAt f a : ℂ)*q a := by
      rw [DiffContOnCl.circleIntegral_eq_zero hR.le
        (hqg.differentiableOn.diffContOnCl_ball subset_rfl),zero_add,
        circleIntegral_weighted_logDerivPrincipalParts f s hR hq hs]

end NLS.ComplexAnalysis
