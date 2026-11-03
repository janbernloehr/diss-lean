import NLS.ComplexAnalysis.SimplePoleQuotient
import NLS.ComplexAnalysis.CauchyFiniteHoles

/-! # The actual circle integral and bound of a single simple residue -/
noncomputable section
open Set Metric Complex
open scoped Classical
namespace NLS.ComplexAnalysis

theorem circleIntegral_simpleQuotient_one_zero {f g : ℂ → ℂ} {c a : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (ha : a ∈ ball c R)
    (hzero : g a = 0) (hsimple : deriv g a ≠ 0)
    (hcover : ∀ z ∈ closedBall c R, g z = 0 → z = a) :
    (∮ z in C(c,R), f z/g z) = (2*Real.pi*I)*(f a/deriv g a) := by
  let s : Finset ℂ := {a}
  let H := toMeromorphicNFOn (fun z => f z/g z-simpleQuotientPrincipalParts f g s z) (closedBall c R)
  have hzs : ∀ z ∈ s, g z = 0 := by intro z hz; have he : z = a := Finset.mem_singleton.mp hz; rwa [he]
  have hds : ∀ z ∈ s, deriv g z ≠ 0 := by intro z hz; have he : z = a := Finset.mem_singleton.mp hz; rwa [he]
  have hcs : ∀ z ∈ closedBall c R, g z = 0 → z ∈ s := by
    intro z hz hgz
    exact Finset.mem_singleton.mpr (hcover z hz hgz)
  have hH : AnalyticOnNhd ℂ H (closedBall c R) :=
    analyticOnNhd_simpleQuotient_remainder hf hg s hzs hds hcs
  have hzH : (∮ z in C(c,R), H z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty hH.continuousOn
      (fun z hz => (hH z (ball_subset_closedBall hz.1)).differentiableAt)
  have hi : CircleIntegrable (fun z : ℂ => (f a/deriv g a)/(z-a)) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hx : AnalyticAt ℂ (fun z : ℂ => (f a/deriv g a)/(z-a)) z :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz ha))
    exact hx.continuousAt.continuousWithinAt
  calc
    (∮ z in C(c,R), f z/g z) = ∮ z in C(c,R), H z+(f a/deriv g a)/(z-a) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      dsimp only
      have hza : z ≠ a := sphere_disjoint_ball.ne_of_mem hz ha
      have hznot : z ∉ s := by simpa only [s,Finset.mem_singleton] using hza
      have hgz : g z ≠ 0 := fun he => hza (hcover z (sphere_subset_closedBall hz) he)
      have he := simpleQuotient_remainder_normalForm_eq hf hg s (sphere_subset_closedBall hz) hznot hgz
      change H z = f z/g z-simpleQuotientPrincipalParts f g s z at he
      simp only [simpleQuotientPrincipalParts,s,Finset.sum_singleton] at he
      rw [he]
      ring
    _ = (2*Real.pi*I)*(f a/deriv g a) := by
      rw [circleIntegral.integral_add ((hH.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le) hi,hzH,zero_add]
      simp only [div_eq_mul_inv,circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball ha]
      ring

theorem norm_simpleQuotientResidue_le {f g : ℂ → ℂ} {c a : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (ha : a ∈ ball c R)
    (hzero : g a = 0) (hsimple : deriv g a ≠ 0)
    (hcover : ∀ z ∈ closedBall c R, g z = 0 → z = a)
    (hbound : ∀ z ∈ sphere c R, ‖f z/g z‖ ≤ M) :
    ‖f a/deriv g a‖ ≤ R*M := by
  have hi := circleIntegral.norm_integral_le_of_norm_le_const hR.le hbound
  rw [circleIntegral_simpleQuotient_one_zero hR hf hg ha hzero hsimple hcover,norm_mul] at hi
  have hnorm : ‖(2*Real.pi*I:ℂ)‖ = 2*Real.pi := by
    simp only [norm_mul,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_I,mul_one]
  rw [hnorm] at hi
  nlinarith [Real.pi_pos]

end NLS.ComplexAnalysis
