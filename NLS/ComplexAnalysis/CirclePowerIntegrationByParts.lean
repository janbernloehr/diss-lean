import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts

/-! # Power integration by parts on a circle

Only analyticity near the contour is required. Both functions may have
singularities inside the circle.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem circleIntegral_power_mul_deriv (F G : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : AnalyticOnNhd ℂ F (sphere c r)) (hG : AnalyticOnNhd ℂ G (sphere c r)) (m : ℕ) :
    (∮ z in C(c,r), F z^m*deriv F z*G z) =
      -((m+1 : ℂ)⁻¹)*(∮ z in C(c,r), F z^(m+1)*deriv G z) := by
  have hzero : (∮ z in C(c,r),
      (m+1 : ℂ)*(F z^m*deriv F z*G z)+F z^(m+1)*deriv G z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr
    intro z hz
    have hd := ((hF z hz).differentiableAt.hasDerivAt.pow (m+1)).mul
      (hG z hz).differentiableAt.hasDerivAt
    simpa only [Pi.mul_apply,Pi.pow_apply,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_assoc]
      using hd.hasDerivWithinAt
  have hi1 : CircleIntegrable (fun z => (m+1 : ℂ)*(F z^m*deriv F z*G z)) c r :=
    (continuousOn_const.mul (((hF.pow m).continuousOn.mul hF.deriv.continuousOn).mul hG.continuousOn)).circleIntegrable hr
  have hi2 : CircleIntegrable (fun z => F z^(m+1)*deriv G z) c r :=
    ((hF.pow (m+1)).continuousOn.mul hG.deriv.continuousOn).circleIntegrable hr
  rw [circleIntegral.integral_add hi1 hi2,circleIntegral.integral_const_mul] at hzero
  have hm : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp
  linear_combination hzero

end NLS.ComplexAnalysis
