import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Primitive actions and cubic moments in the KdV Hamiltonian

These are the literal contour quantities in (4.8) and the integration by
parts preceding (4.12) of arXiv:1502.05857v1. Circles have counterclockwise
orientation. The normalized primitive is an input function: this module
does not construct the Hill discriminant or identify its spectral branch.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

/-- The action after closed-contour integration by parts, with factor -1/pi. -/
def primitiveAction (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∮ z in C(c,r), F z

/-- The cubic normalized primitive moment, with factor 1/pi and no factor i. -/
def cubicMoment (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∮ z in C(c,r), F z ^ 3

/-- The primitive action is the original lambda-weighted derivative period.
Only analyticity near the integration circle is needed, not inside its gap. -/
theorem primitiveAction_eq_derivative_period
    (F : ℂ → ℂ) (D : Set ℂ) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hcircle : sphere c r ⊆ D) :
    primitiveAction F c r =
      (Real.pi : ℂ)⁻¹ * ∮ z in C(c,r), z * deriv F z := by
  rw [ComplexAnalysis.circleIntegral_mul_deriv_eq_neg_of_analyticOnNhd F D hF c r hr hcircle]
  unfold primitiveAction
  ring

/-- The indexed additive normalization of a primitive leaves its action
period unchanged. Only analyticity near the actual contour is needed. -/
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

/-- A primitive analytic through a closed gap has zero cubic contour moment. -/
theorem cubicMoment_eq_zero_of_analyticOnNhd
    (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : AnalyticOnNhd ℂ F (closedBall c r)) : cubicMoment F c r = 0 := by
  have hpow := hF.pow 3
  have hz : (∮ z in C(c,r), F z ^ 3) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
      hpow.continuousOn (fun z hz => (hpow z (ball_subset_closedBall hz.1)).differentiableAt)
  simp only [cubicMoment, hz, mul_zero]

/-- The cubic contour moment of a primitive bounded by A on a radius-r
circle obeys the exact estimate |R| <= 2*r*A^3. -/
theorem norm_cubicMoment_le (F : ℂ → ℂ) (c : ℂ) (r A : ℝ) (hr : 0 ≤ r)
    (hF : ∀ z ∈ sphere c r, ‖F z‖ ≤ A) :
    ‖cubicMoment F c r‖ ≤ 2 * r * A ^ 3 := by
  have hi : ‖∮ z in C(c,r), F z ^ 3‖ ≤ 2 * Real.pi * r * A ^ 3 := by
    apply circleIntegral.norm_integral_le_of_norm_le_const hr
    intro z hz
    rw [norm_pow]
    gcongr
    exact hF z hz
  calc
    ‖cubicMoment F c r‖ = Real.pi⁻¹ * ‖∮ z in C(c,r), F z ^ 3‖ := by
      simp only [cubicMoment, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    _ ≤ Real.pi⁻¹ * (2 * Real.pi * r * A ^ 3) := by gcongr
    _ = 2 * r * A ^ 3 := by field_simp

/-- A primitive bound of order gamma/n, a contour radius of order gamma,
and the gap/action bound gamma^2/n <= K*|I| imply the complex-neighborhood
quadratic action estimate needed in Proposition 4.7(ii). -/
theorem norm_weighted_cubicMoment_le_action_sq
    (F : ℂ → ℂ) (c : ℂ) (r gamma A B K n : ℝ) (a : ℂ)
    (hr : 0 ≤ r) (hgamma : 0 ≤ gamma) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hn : 0 < n) (hradius : r ≤ B * gamma)
    (hF : ∀ z ∈ sphere c r, ‖F z‖ ≤ A * gamma / n)
    (ha : gamma ^ 2 / n ≤ K * ‖a‖) :
    ‖((8 * n * Real.pi : ℝ) : ℂ) * cubicMoment F c r‖ ≤
      (16 * Real.pi * B * A ^ 3 * K ^ 2) * ‖a‖ ^ 2 := by
  have hbound := norm_cubicMoment_le F c r (A * gamma / n) hr hF
  calc
    ‖((8 * n * Real.pi : ℝ) : ℂ) * cubicMoment F c r‖ =
        (8 * n * Real.pi) * ‖cubicMoment F c r‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ (8 * n * Real.pi) * (2 * r * (A * gamma / n) ^ 3) := by
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (8 * n * Real.pi) * (2 * (B * gamma) * (A * gamma / n) ^ 3) := by
      gcongr
    _ = (16 * Real.pi * B * A ^ 3) * (gamma ^ 2 / n) ^ 2 := by
      field_simp
      ring
    _ ≤ (16 * Real.pi * B * A ^ 3) * (K * ‖a‖) ^ 2 := by gcongr
    _ = (16 * Real.pi * B * A ^ 3 * K ^ 2) * ‖a‖ ^ 2 := by ring

/-- Joint analytic dependence of a normalized primitive gives Banach-analytic
cubic moments on every parameter neighborhood with one fixed contour. -/
theorem analyticOnNhd_cubicMoment
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : ℂ × E → ℂ) (D : Set (ℂ × E)) (hD : IsOpen D)
    (hF : AnalyticOnNhd ℂ F D) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (V : Set E) (hV : IsOpen V)
    (hcircle : ∀ a ∈ V, ∀ z ∈ sphere c r, (z,a) ∈ D) :
    AnalyticOnNhd ℂ (fun a => cubicMoment (fun z => F (z,a)) c r) V := by
  have hi := ComplexAnalysis.analyticOnNhd_circleIntegral_of_jointAnalytic
    (fun p => F p ^ 3) hD (hF.pow 3) c r hr hV hcircle
  intro a ha
  exact (hi a ha).const_smul (c := (Real.pi : ℂ)⁻¹)

end NLS.KdV
