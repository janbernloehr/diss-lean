import NLS.ComplexAnalysis.SimplePoleQuotient

/-! # Finite Cauchy interpolation at simple denominator zeros

The interpolation error is exactly the outer-circle Cauchy integral.
The finite principal parts have zero Cauchy-kernel integral because both
of each term's two poles lie inside the same circle.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.ComplexAnalysis

/-- A simple principal part has zero Cauchy-kernel integral when its
pole and the evaluation point are distinct and both enclosed. -/
theorem circleIntegral_two_enclosed_poles {c a w b : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : a ∈ ball c R) (hw : w ∈ ball c R) (haw : a ≠ w) :
    (∮ z in C(c,R), b/(z-a)/(z-w)) = 0 := by
  have hi (q : ℂ) (hq : q ∈ ball c R) :
      CircleIntegrable (fun z : ℂ => (z-q)⁻¹) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have ha : AnalyticAt ℂ (fun z : ℂ => (z-q)⁻¹) z :=
      (analyticAt_id.sub analyticAt_const).inv
        (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hq))
    exact ha.continuousAt.continuousWithinAt
  calc
    (∮ z in C(c,R), b/(z-a)/(z-w)) =
        ∮ z in C(c,R), (b/(a-w))*((z-a)⁻¹-(z-w)⁻¹) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      dsimp only
      have hza : z-a ≠ 0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz ha)
      have hzw : z-w ≠ 0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hw)
      field_simp [hza,hzw,sub_ne_zero.mpr haw]
      ring
    _ = 0 := by
      rw [circleIntegral.integral_const_mul,circleIntegral.integral_sub (hi a ha) (hi w hw),
        circleIntegral.integral_sub_inv_of_mem_ball ha,circleIntegral.integral_sub_inv_of_mem_ball hw,
        sub_self,mul_zero]

/-- Finite principal parts do not contribute to the outer Cauchy integral. -/
theorem circleIntegral_simplePrincipalParts_cauchy_eq_zero (f g : ℂ → ℂ)
    (s : Finset ℂ) {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hs : (s : Set ℂ) ⊆ ball c R) (hw : w ∈ ball c R) (hws : w ∉ s) :
    (∮ z in C(c,R), simpleQuotientPrincipalParts f g s z/(z-w)) = 0 := by
  have hi : ∀ a ∈ s, CircleIntegrable (fun z : ℂ => (f a/deriv g a)/(z-a)/(z-w)) c R := by
    intro a ha
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hza : z-a ≠ 0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz (hs ha))
    have hzw : z-w ≠ 0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hw)
    have ha : AnalyticAt ℂ (fun z : ℂ => (f a/deriv g a)/(z-a)/(z-w)) z :=
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hza).div
        (analyticAt_id.sub analyticAt_const) hzw
    exact ha.continuousAt.continuousWithinAt
  calc
    (∮ z in C(c,R), simpleQuotientPrincipalParts f g s z/(z-w)) =
        ∮ z in C(c,R), ∑ a ∈ s, (f a/deriv g a)/(z-a)/(z-w) := by
      simp only [simpleQuotientPrincipalParts,Finset.sum_div]
    _ = ∑ a ∈ s, ∮ z in C(c,R), (f a/deriv g a)/(z-a)/(z-w) :=
      circleIntegral.integral_fun_sum hi
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      exact circleIntegral_two_enclosed_poles hR (hs ha) hw
        (fun he => hws (he ▸ ha))

/-- The exact finite interpolation error for an analytic numerator and
simple denominator zeros, with their residues derived from derivatives. -/
theorem circleIntegral_simpleQuotient_cauchy_eq_interpolation_error
    {f g : ℂ → ℂ} {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (s : Finset ℂ) (hs : (s : Set ℂ) ⊆ ball c R)
    (hzero : ∀ a ∈ s, g a = 0) (hsimple : ∀ a ∈ s, deriv g a ≠ 0)
    (hcover : ∀ z ∈ closedBall c R, g z = 0 → z ∈ s)
    (hw : w ∈ ball c R) (hgw : g w ≠ 0) :
    (∮ z in C(c,R), f z/g z/(z-w)) =
      (2*Real.pi*I)*(f w/g w-simpleQuotientPrincipalParts f g s w) := by
  let H := toMeromorphicNFOn
    (fun z => f z/g z-simpleQuotientPrincipalParts f g s z) (closedBall c R)
  have hH : AnalyticOnNhd ℂ H (closedBall c R) :=
    analyticOnNhd_simpleQuotient_remainder hf hg s hzero hsimple hcover
  have hws : w ∉ s := fun he => hgw (hzero w he)
  have hboundary (z : ℂ) (hz : z ∈ sphere c R) : z ∉ s ∧ g z ≠ 0 := by
    have hzs : z ∉ s := fun he => sphere_disjoint_ball.le_bot ⟨hz,hs he⟩
    exact ⟨hzs,fun he => hzs (hcover z (sphere_subset_closedBall hz) he)⟩
  have hiH : CircleIntegrable (fun z => H z/(z-w)) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact ((hH z (sphere_subset_closedBall hz)).div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hw))).continuousAt.continuousWithinAt
  have hiP : CircleIntegrable (fun z => simpleQuotientPrincipalParts f g s z/(z-w)) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact ((analyticAt_simpleQuotientPrincipalParts f g s (hboundary z hz).1).div
      (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hw))).continuousAt.continuousWithinAt
  calc
    (∮ z in C(c,R), f z/g z/(z-w)) =
        ∮ z in C(c,R), H z/(z-w)+simpleQuotientPrincipalParts f g s z/(z-w) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      dsimp only
      rw [show H z = f z/g z-simpleQuotientPrincipalParts f g s z from
        simpleQuotient_remainder_normalForm_eq hf hg s (sphere_subset_closedBall hz)
          (hboundary z hz).1 (hboundary z hz).2]
      ring
    _ = (∮ z in C(c,R), H z/(z-w))+
        ∮ z in C(c,R), simpleQuotientPrincipalParts f g s z/(z-w) :=
      circleIntegral.integral_add hiH hiP
    _ = (2*Real.pi*I)*H w := by
      rw [circleIntegral_simplePrincipalParts_cauchy_eq_zero f g s hR hs hw hws,add_zero]
      simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
        hH.differentiableOn.circleIntegral_sub_inv_smul hw
    _ = (2*Real.pi*I)*(f w/g w-simpleQuotientPrincipalParts f g s w) := by
      rw [show H w = f w/g w-simpleQuotientPrincipalParts f g s w from
        simpleQuotient_remainder_normalForm_eq hf hg s (ball_subset_closedBall hw) hws hgw]

end NLS.ComplexAnalysis
