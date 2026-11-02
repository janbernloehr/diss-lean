import NLS.KdV.ActionHamiltonianMoments

/-! # The quartic gap-period identity for the KdV Hamiltonian

This proves the contour calculation in equation (4.12) of
arXiv:1502.05857v1. Analytic continuation of F_n^2 through the gap kills
the even powers. The odd terms then give the exact coefficients
8*n^3*pi^3*I_n and 8*n*pi*R_n.

This is a contour theorem, not the missing identification of the exterior
Laurent coefficient with the physical KdV energy.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

/-- Analyticity of the square through a gap kills every even contour moment. -/
theorem even_period_eq_zero (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r)) (k : ℕ) :
    (∮ z in C(c,r), F z ^ (2 * k)) = 0 := by
  have hp : AnalyticOnNhd ℂ (fun z => F z ^ (2 * k)) (closedBall c r) := by
    simpa only [Pi.pow_apply, pow_mul] using! hF.pow k
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
    hp.continuousOn (fun z hz => (hp z (ball_subset_closedBall hz.1)).differentiableAt)

/-- Only the odd powers of the normalized primitive contribute to the
quartic period. The assumptions give integrability and even-period
vanishing as proved facts, not supplied integral identities. -/
theorem quartic_shift_period (F : ℂ → ℂ) (c s : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hcont : ContinuousOn F (sphere c r))
    (hF : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r)) :
    (∮ z in C(c,r), (F z - s) ^ 4) =
      -4 * s * (∮ z in C(c,r), F z ^ 3) -
        4 * s ^ 3 * (∮ z in C(c,r), F z) := by
  let coeff : ℕ → ℂ := fun k => (Nat.choose 4 k : ℂ) * (-s) ^ (4-k)
  have hexp : (fun z => (F z - s) ^ 4) =
      (fun z => ∑ k ∈ Finset.range 5, coeff k * F z ^ k) := by
    funext z
    norm_num [coeff, Finset.sum_range_succ, show Nat.choose 4 2 = 6 by decide]
    ring
  have hi (k : ℕ) : CircleIntegrable (fun z => coeff k * F z ^ k) c r :=
    (continuousOn_const.mul (hcont.pow k)).circleIntegrable hr
  have hzero : (∮ z in C(c,r), (1 : ℂ)) = 0 := by
    simpa using even_period_eq_zero F c r hr hF 0
  have htwo : (∮ z in C(c,r), F z ^ 2) = 0 := by
    simpa using even_period_eq_zero F c r hr hF 1
  have hfour : (∮ z in C(c,r), F z ^ 4) = 0 := by
    simpa using even_period_eq_zero F c r hr hF 2
  rw [hexp, circleIntegral.integral_fun_sum (fun k _ => hi k)]
  simp [Finset.sum_range_succ, coeff, circleIntegral.integral_const_mul,
    hzero, htwo, hfour]
  ring

/-- The exact single-gap identity (4.12), with counterclockwise contour
normalization and the action recovered by integration by parts. -/
theorem quartic_gap_contribution (F : ℂ → ℂ) (c : ℂ) (r n : ℝ) (hr : 0 ≤ r)
    (hcont : ContinuousOn F (sphere c r))
    (hF : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r)) :
    (-4 : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(c,r), (F z - I * (n : ℂ) * Real.pi) ^ 4) =
      ((8 * n ^ 3 * Real.pi ^ 3 : ℝ) : ℂ) * primitiveAction F c r +
        ((8 * n * Real.pi : ℝ) : ℂ) * cubicMoment F c r := by
  rw [quartic_shift_period F c (I * (n : ℂ) * Real.pi) r hr hcont hF]
  unfold primitiveAction cubicMoment
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring

end NLS.KdV
