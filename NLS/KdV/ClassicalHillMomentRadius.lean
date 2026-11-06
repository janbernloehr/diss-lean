import NLS.KdV.ClassicalHillAnnulusCoverage
import NLS.KdV.ClassicalHighContourMoments

/-! # Shrinking the actual Hill moment's frequency circle

The entire closed high annulus belongs to the already constructed source
domain. Cauchy-Goursat therefore equates the literal moment on the original
quarter-pi circle with its value on every prescribed smaller positive
circle. The exact energy Jacobian 2*z is retained.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_classicalHill_high_power_period_radius_independence
    (q : Curve ℂ) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      (∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          r ≤ ‖z-(Real.pi : ℂ)*(n : ℕ)‖ → (z^2,a) ∈ classicalHillContinuationDomain) ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ rho ∈ Icc r (Real.pi/4), ∀ m : ℕ,
          ((Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4),
            (classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m*(2*z)) =
            (Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),rho),
              (classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m*(2*z) := by
  obtain ⟨N,V,hN,hV,hq,hcover⟩ := exists_classicalHill_high_annulus_neighborhood q r hr hrpi
  refine ⟨N,V,hN,hV,hq,hcover,?_⟩
  intro a ha n hn rho hrho m
  let c : ℂ := (Real.pi : ℂ)*(n : ℕ)
  let f : ℂ → ℂ := fun z =>
    (classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m*(2*z)
  have hf : AnalyticOnNhd ℂ f (closedBall c (Real.pi/4) \ ball c rho) := by
    intro z hz
    have hfar : r ≤ ‖z-c‖ := hrho.1.trans (by
      simpa only [mem_ball,dist_eq_norm,not_lt] using hz.2)
    have hdom := hcover a ha n hn z hz.1 hfar
    have hF : AnalyticAt ℂ (fun z => classicalHillFrequencyPrimitive (z,a)) z :=
      (analyticOnNhd_classicalHillFrequencyPrimitive (z,a) hdom).comp
        (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
    exact ((hF.add analyticAt_const).pow m).mul (analyticAt_const.mul analyticAt_id)
  have heq := circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (hr.trans_le hrho.1) hrho.2 countable_empty hf.continuousOn (fun z hz =>
      (hf z ⟨ball_subset_closedBall hz.1.1,fun hh => hz.1.2 (ball_subset_closedBall hh)⟩).differentiableAt)
  exact congrArg (fun w : ℂ => (Real.pi : ℂ)⁻¹*w) heq


theorem exists_classicalHill_high_moment_radius_independence
    (q : Curve ℂ) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      (∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          r ≤ ‖z-(Real.pi : ℂ)*(n : ℕ)‖ → (z^2,a) ∈ classicalHillContinuationDomain) ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ rho ∈ Icc r (Real.pi/4),
          classicalHillHighContourMoment n a =
            (Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),rho),
              (classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi)^3*(2*z) := by
  obtain ⟨N,V,hN,hV,hq,hcover,heq⟩ :=
    exists_classicalHill_high_power_period_radius_independence q r hr hrpi
  refine ⟨N,V,hN,hV,hq,hcover,?_⟩
  intro a ha n hn rho hrho
  exact heq a ha n hn rho hrho 3

end NLS.KdV
