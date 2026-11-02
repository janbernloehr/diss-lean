import NLS.ComplexAnalysis.ParametricCircleIntegralHigher
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # Weighted primitive moments for the KdV frequency formulas

The literal moment in arXiv:1605.06690v1, Section 3, is the contour integral
of F_k^m times psi_n/sqrt(Delta^2-4). This module retains that integrand and
counterclockwise circle orientation. It proves the analytic and parity
calculations from local analytic continuation properties. It does not
construct the Hill discriminant, its branch, or the normalized psi functions.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

def frequencyMoment (F G : ℂ → ℂ) (c : ℂ) (r : ℝ) (m : ℕ) : ℂ :=
  ∮ z in C(c,r), F z ^ m * G z

theorem analyticOnNhd_frequencyMoment
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F G : ℂ × E → ℂ) (D : Set (ℂ × E)) (hD : IsOpen D)
    (hF : AnalyticOnNhd ℂ F D) (hG : AnalyticOnNhd ℂ G D)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (V : Set E) (hV : IsOpen V)
    (hcircle : ∀ a ∈ V, ∀ z ∈ sphere c r, (z,a) ∈ D) (m : ℕ) :
    AnalyticOnNhd ℂ (fun a => frequencyMoment (fun z => F (z,a)) (fun z => G (z,a)) c r m) V :=
  ComplexAnalysis.analyticOnNhd_circleIntegral_of_jointAnalytic
    (fun p => F p ^ m * G p) hD ((hF.pow m).mul hG) c r hr hV hcircle

/-- Analytic continuation of F^2 and F*G through the gap kills every odd
weighted moment. Individual zero-period identities are not assumptions. -/
theorem frequencyMoment_odd_eq_zero (F G : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF2 : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r))
    (hFG : AnalyticOnNhd ℂ (fun z => F z * G z) (closedBall c r)) (l : ℕ) :
    frequencyMoment F G c r (2 * l + 1) = 0 := by
  have hp : AnalyticOnNhd ℂ (fun z => F z ^ (2 * l + 1) * G z) (closedBall c r) := by
    simpa only [Pi.mul_apply, Pi.pow_apply, pow_add, pow_one, pow_mul, mul_assoc] using!
      (hF2.pow l).mul hFG
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
    hp.continuousOn (fun z hz => (hp z (ball_subset_closedBall hz.1)).differentiableAt)

/-- Circle agreement with analytic filled extensions suffices; no values
of the unfilled quotient are prescribed at its branch points. -/
theorem frequencyMoment_odd_eq_zero_of_continuations
    (F G K H : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hK : AnalyticOnNhd ℂ K (closedBall c r)) (hH : AnalyticOnNhd ℂ H (closedBall c r))
    (hmatch : ∀ z ∈ sphere c r, K z = F z^2 ∧ H z = F z*G z) (l : ℕ) :
    frequencyMoment F G c r (2*l+1) = 0 := by
  have ha : AnalyticOnNhd ℂ (fun z => K z^l*H z) (closedBall c r) := (hK.pow l).mul hH
  unfold frequencyMoment
  rw [circleIntegral.integral_congr hr (fun z hz => ?_)]
  · exact circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
      ha.continuousOn (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)
  · rw [(hmatch z hz).1,(hmatch z hz).2]
    rw [pow_add,pow_mul,pow_one]
    ring

/-- Filled analytic circle extensions of the primitive and its product
with the differential kill every positive moment. -/
theorem frequencyMoment_pos_eq_zero_of_continuations
    (F G J H : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hJ : AnalyticOnNhd ℂ J (closedBall c r)) (hH : AnalyticOnNhd ℂ H (closedBall c r))
    (hmatch : ∀ z ∈ sphere c r, J z = F z ∧ H z = F z*G z) (m : ℕ) :
    frequencyMoment F G c r (m+1) = 0 := by
  have ha : AnalyticOnNhd ℂ (fun z => J z^m*H z) (closedBall c r) := (hJ.pow m).mul hH
  unfold frequencyMoment
  rw [circleIntegral.integral_congr hr (fun z hz => ?_)]
  · exact circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
      ha.continuousOn (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)
  · rw [(hmatch z hz).1,(hmatch z hz).2,pow_succ]
    ring

/-- When F itself continues analytically through a collapsed gap, and its
product with G does too, all positive moments vanish, including the
diagonal case where G alone may still have a pole. -/
theorem frequencyMoment_pos_eq_zero (F G : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : AnalyticOnNhd ℂ F (closedBall c r))
    (hFG : AnalyticOnNhd ℂ (fun z => F z * G z) (closedBall c r)) (m : ℕ) :
    frequencyMoment F G c r (m + 1) = 0 := by
  have hp : AnalyticOnNhd ℂ (fun z => F z ^ (m + 1) * G z) (closedBall c r) := by
    simpa only [Pi.mul_apply, Pi.pow_apply, pow_succ, mul_assoc] using! (hF.pow m).mul hFG
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
    hp.continuousOn (fun z hz => (hp z (ball_subset_closedBall hz.1)).differentiableAt)

theorem norm_frequencyMoment_le (F G : ℂ → ℂ) (c : ℂ) (r A B : ℝ)
    (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hF : ∀ z ∈ sphere c r, ‖F z‖ ≤ A) (hG : ∀ z ∈ sphere c r, ‖G z‖ ≤ B) (m : ℕ) :
    ‖frequencyMoment F G c r m‖ ≤ 2 * Real.pi * r * (A ^ m * B) := by
  apply circleIntegral.norm_integral_le_of_norm_le_const hr
  intro z hz
  rw [norm_mul, norm_pow]
  gcongr
  · exact hF z hz
  · exact hG z hz

/-- Binomial expansion under the actual contour integral. -/
theorem shifted_frequency_period (F G : ℂ → ℂ) (c s : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : ContinuousOn F (sphere c r)) (hG : ContinuousOn G (sphere c r)) (d : ℕ) :
    (∮ z in C(c,r), (F z - s) ^ d * G z) =
      ∑ m ∈ Finset.range (d + 1), (Nat.choose d m : ℂ) * (-s) ^ (d - m) *
        frequencyMoment F G c r m := by
  have he : (fun z => (F z - s) ^ d * G z) =
      fun z => ∑ m ∈ Finset.range (d + 1),
        ((Nat.choose d m : ℂ) * (-s) ^ (d - m)) * (F z ^ m * G z) := by
    funext z
    rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hi (m : ℕ) : CircleIntegrable (fun z =>
      ((Nat.choose d m : ℂ) * (-s) ^ (d - m)) * (F z ^ m * G z)) c r :=
    (continuousOn_const.mul ((hF.pow m).mul hG)).circleIntegrable hr
  rw [he, circleIntegral.integral_fun_sum (fun m _ => hi m)]
  simp only [frequencyMoment, circleIntegral.integral_const_mul]

theorem cubic_shift_frequency_period (F G : ℂ → ℂ) (c s : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : ContinuousOn F (sphere c r)) (hG : ContinuousOn G (sphere c r))
    (hF2 : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r))
    (hFG : AnalyticOnNhd ℂ (fun z => F z * G z) (closedBall c r)) :
    (∮ z in C(c,r), (F z - s) ^ 3 * G z) =
      -3 * s * frequencyMoment F G c r 2 - s ^ 3 * frequencyMoment F G c r 0 := by
  have h1 : frequencyMoment F G c r 1 = 0 := by
    simpa using frequencyMoment_odd_eq_zero F G c r hr hF2 hFG 0
  have h3 : frequencyMoment F G c r 3 = 0 := by
    simpa using frequencyMoment_odd_eq_zero F G c r hr hF2 hFG 1
  rw [shifted_frequency_period F G c s r hr hF hG 3]
  norm_num [Finset.sum_range_succ, h1, h3]
  ring

theorem fifth_shift_frequency_period (F G : ℂ → ℂ) (c s : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : ContinuousOn F (sphere c r)) (hG : ContinuousOn G (sphere c r))
    (hF2 : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r))
    (hFG : AnalyticOnNhd ℂ (fun z => F z * G z) (closedBall c r)) :
    (∮ z in C(c,r), (F z - s) ^ 5 * G z) =
      -5 * s * frequencyMoment F G c r 4 -
        10 * s ^ 3 * frequencyMoment F G c r 2 - s ^ 5 * frequencyMoment F G c r 0 := by
  have h1 : frequencyMoment F G c r 1 = 0 := by
    simpa using frequencyMoment_odd_eq_zero F G c r hr hF2 hFG 0
  have h3 : frequencyMoment F G c r 3 = 0 := by
    simpa using frequencyMoment_odd_eq_zero F G c r hr hF2 hFG 1
  have h5 : frequencyMoment F G c r 5 = 0 := by
    simpa using frequencyMoment_odd_eq_zero F G c r hr hF2 hFG 2
  rw [shifted_frequency_period F G c s r hr hF hG 5]
  norm_num [Finset.sum_range_succ, h1, h3, h5, show Nat.choose 5 2 = 10 by decide,
    show Nat.choose 5 3 = 10 by decide]
  ring

end NLS.KdV
