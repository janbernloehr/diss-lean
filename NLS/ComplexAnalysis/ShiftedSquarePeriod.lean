import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Polynomial contour periods of a shifted square

If the square fills the enclosed gap analytically, only the linear
term of a constant shift contributes to the contour integral.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem circleIntegral_pow_mul_shifted_square (F : ℂ → ℂ) (s c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hF : ContinuousOn F (sphere c r))
    (hSq : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r)) (m : ℕ) :
    (∮ z in C(c, r), z ^ m * (F z - s) ^ 2) =
      -2 * s * ∮ z in C(c, r), z ^ m * F z := by
  have hzero : (∮ z in C(c, r), z ^ m * F z ^ 2) = 0 := by
    have ha : AnalyticOnNhd ℂ (fun z => z ^ m * F z ^ 2) (closedBall c r) :=
      (analyticOnNhd_id.pow m).mul hSq
    exact circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
      ha.continuousOn (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)
  have hpoly : (∮ z in C(c, r), z ^ m) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
      (continuousOn_id.pow m) (fun z _ => differentiableAt_id.pow m)
  have hi₀ : CircleIntegrable (fun z => z ^ m * F z ^ 2) c r :=
    ((continuousOn_id.pow m).mul (hF.pow 2)).circleIntegrable hr
  have hi₁ : CircleIntegrable (fun z => (-2 * s) * (z ^ m * F z)) c r :=
    (continuousOn_const.mul ((continuousOn_id.pow m).mul hF)).circleIntegrable hr
  have hi₂ : CircleIntegrable (fun z : ℂ => s ^ 2 * z ^ m) c r :=
    (continuousOn_const.mul (continuousOn_id.pow m)).circleIntegrable hr
  have hi₀₁ : CircleIntegrable (fun z => z ^ m * F z ^ 2 + (-2 * s) * (z ^ m * F z)) c r :=
    hi₀.add hi₁
  have he : (fun z => z ^ m * (F z - s) ^ 2) =
      (fun z => (z ^ m * F z ^ 2 + (-2 * s) * (z ^ m * F z)) + s ^ 2 * z ^ m) := by
    funext z
    ring
  rw [he, circleIntegral.integral_add hi₀₁ hi₂, circleIntegral.integral_add hi₀ hi₁,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul, hzero, hpoly,
    mul_zero, add_zero, zero_add]

end NLS.ComplexAnalysis
