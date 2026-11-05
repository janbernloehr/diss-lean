import NLS.ComplexAnalysis.HolomorphicCircleIntegral

/-! A holomorphic weight annihilates the filled square and constant
terms in a shifted square. The remaining contour is exactly twice the
shift times the weighted linear primitive contour. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem circleIntegral_shifted_square_weight (f Q q : ℂ → ℂ) (a c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hf : ContinuousOn f (sphere c R))
    (hQ : AnalyticOnNhd ℂ Q (closedBall c R)) (hq : AnalyticOnNhd ℂ q (closedBall c R))
    (he : EqOn (fun z => f z^2) Q (sphere c R)) :
    (∮ z in C(c,R), q z*(f z+a)^2)=2*a*(∮ z in C(c,R), q z*f z) := by
  have hqQ := hq.mul hQ
  have hzQ : (∮ z in C(c,R), q z*Q z)=0 :=
    (DiffContOnCl.mk_ball (hqQ.differentiableOn.mono ball_subset_closedBall)
      hqQ.continuousOn).circleIntegral_eq_zero hR
  have hzq : (∮ z in C(c,R), q z)=0 :=
    (DiffContOnCl.mk_ball (hq.differentiableOn.mono ball_subset_closedBall)
      hq.continuousOn).circleIntegral_eq_zero hR
  have hciQ : CircleIntegrable (fun z => q z*Q z) c R :=
    (hqQ.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR
  have hciF : CircleIntegrable (fun z => q z*f z) c R :=
    ((hq.continuousOn.mono sphere_subset_closedBall).mul hf).circleIntegrable hR
  have hciq : CircleIntegrable q c R :=
    (hq.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR
  have hci2 : CircleIntegrable (fun z => (2*a)*(q z*f z)) c R := hciF.const_mul (2*a)
  have hcia : CircleIntegrable (fun z => a^2*q z) c R := hciq.const_mul (a^2)
  have hcisum : CircleIntegrable (fun z => q z*Q z+(2*a)*(q z*f z)) c R := hciQ.add hci2
  calc
    _ = ∮ z in C(c,R), q z*Q z+(2*a)*(q z*f z)+a^2*q z := by
      apply circleIntegral.integral_congr hR
      intro z hz
      dsimp only
      rw [← he hz]
      ring
    _ = (∮ z in C(c,R), q z*Q z)+(2*a)*(∮ z in C(c,R), q z*f z)+
        a^2*(∮ z in C(c,R), q z) := by
      rw [circleIntegral.integral_add hcisum hcia,
        circleIntegral.integral_add hciQ hci2]
      simp only [circleIntegral.integral_const_mul]
    _ = _ := by rw [hzQ,hzq,zero_add,mul_zero,add_zero]

end NLS.ComplexAnalysis
