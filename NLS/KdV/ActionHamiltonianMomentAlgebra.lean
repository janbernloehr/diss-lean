import NLS.KdV.ActionHamiltonianMoments

noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem norm_primitiveAction_le (F : ℂ → ℂ) (c : ℂ) (r A : ℝ)
    (hr : 0 ≤ r) (hF : ∀ z ∈ sphere c r, ‖F z‖ ≤ A) :
    ‖primitiveAction F c r‖ ≤ 2*r*A := by
  have hi : ‖∮ z in C(c,r), F z‖ ≤ 2*Real.pi*r*A :=
    circleIntegral.norm_integral_le_of_norm_le_const hr hF
  calc
    _ = Real.pi⁻¹*‖∮ z in C(c,r), F z‖ := by
      simp only [primitiveAction,norm_mul,norm_neg,norm_inv,Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    _ ≤ Real.pi⁻¹*(2*Real.pi*r*A) := by gcongr
    _ = 2*r*A := by field_simp

theorem primitiveAction_sub (F G : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hF : CircleIntegrable F c r) (hG : CircleIntegrable G c r) :
    primitiveAction (fun z => F z-G z) c r = primitiveAction F c r-primitiveAction G c r := by
  unfold primitiveAction
  rw [circleIntegral.integral_sub hF hG]
  ring

theorem primitiveAction_eq_zero_of_analyticOnNhd
    (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : AnalyticOnNhd ℂ F (closedBall c r)) : primitiveAction F c r = 0 := by
  have hz : (∮ z in C(c,r), F z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
      hF.continuousOn (fun z hz => (hF z (ball_subset_closedBall hz.1)).differentiableAt)
  simp only [primitiveAction,hz,mul_zero]

theorem primitiveAction_add_const_of_analyticOnNhd
    (F : ℂ → ℂ) (D : Set ℂ) (hF : AnalyticOnNhd ℂ F D)
    (c k : ℂ) (r : ℝ) (hr : 0 ≤ r) (hcircle : sphere c r ⊆ D) :
    primitiveAction (fun z => F z+k) c r = primitiveAction F c r := by
  have hshift : AnalyticOnNhd ℂ (fun z => F z+k) D := fun z hz => (hF z hz).add analyticAt_const
  rw [primitiveAction_eq_derivative_period (fun z => F z+k) D hshift c r hr hcircle,
    primitiveAction_eq_derivative_period F D hF c r hr hcircle]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  change z*deriv (fun w => F w+k) z = z*deriv F z
  rw [((hF z (hcircle hz)).differentiableAt.hasDerivAt.add_const k).deriv]

end NLS.KdV
