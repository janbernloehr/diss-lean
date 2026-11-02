import NLS.KdV.ClassicalHillMomentRadius
import NLS.KdV.ClassicalHillGapCutRoots
import NLS.ComplexAnalysis.SquaredCircleHomotopy
import Mathlib.Analysis.Normed.Module.Connected

/-! # The actual high cubic moment is a cut-root circle moment

A connected small frequency circle fixes one physical sign. The exact
squared-circle homotopy then moves that integral to an energy circle
inside the domain of the analytic cut root. This suffices for moment
estimates without assuming a sign on every source-overlap component.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem classicalHill_power_period_eq_signed_cut_period
    (a : Curve ℂ) (n : ℕ+) (r : ℝ) (K B : ℂ → ℂ) (l u : ℂ) (m : ℕ) (P : ℂ)
    (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (hl : l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8))
    (hu : u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8))
    (hB : AnalyticOnNhd ℂ B
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hsq : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u,
      B z ≠ 0 ∧ B z^2 = K z)
    (hmatch : ∀ z ∈ classicalHillGapSquareDisc n r, (z,a) ∈ classicalHillContinuationDomain →
      K z = (classicalHillContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^2)
    (hsource : ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (r/4),
      (z^2,a) ∈ classicalHillContinuationDomain)
    (hmoment : P =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),r/4),
        (classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m*(2*z)) :
    ∃ k : ℂ, (k = 1 ∨ k = -1) ∧
      P = k^m * ((Real.pi : ℂ)⁻¹ *
        ∮ z in C((((Real.pi : ℂ)*(n : ℕ))^2),Real.pi*(n : ℕ)*r/2), B z^m) := by
  let c : ℝ := Real.pi*(n : ℕ)
  let R : ℝ := c*r
  let rho : ℝ := r/4
  let E : ℂ := (c : ℂ)^2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hR : 0 < R := mul_pos hc hr
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrhoc : rho ≤ c/8 := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    dsimp only [rho,c]
    nlinarith [Real.pi_pos]
  have hB' : AnalyticOnNhd ℂ B (ball E R \ segment ℝ l u) := by
    simpa only [E,R,c,ofReal_mul,ofReal_natCast] using hB
  have hseg : segment ℝ l u ⊆ ball E (R/8) := (convex_ball _ _).segment_subset
    (by simpa only [E,R,c,ofReal_mul,ofReal_natCast] using hl)
    (by simpa only [E,R,c,ofReal_mul,ofReal_natCast] using hu)
  have hshell (z : ℂ) (hz : z ∈ sphere (c : ℂ) rho) :
      z^2 ∈ ball E R \ segment ℝ l u := by
    have hh := norm_sq_sub_sq_of_small_sphere c rho hc hrho hrhoc z hz
    have hlow : R/4 < ‖z^2-E‖ := by simpa only [R,E,rho,mul_div_assoc] using hh.1
    have hhigh : ‖z^2-E‖ ≤ 3*R/4 := by
      convert hh.2 using 1
      dsimp only [R,rho,E]
      ring
    refine ⟨by rw [mem_ball,dist_eq_norm]; linarith,?_⟩
    intro he
    have hh' : ‖z^2-E‖ < R/8 := by simpa only [mem_ball,dist_eq_norm] using hseg he
    linarith
  let F : ℂ → ℂ := fun z => classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi
  let G : ℂ → ℂ := fun z => B (z^2)
  have hsource' (z : ℂ) (hz : z ∈ sphere (c : ℂ) rho) :
      (z^2,a) ∈ classicalHillContinuationDomain :=
    hsource z (by simpa only [c,rho,ofReal_mul,ofReal_natCast] using hz)
  have hF : AnalyticOnNhd ℂ F (sphere (c : ℂ) rho) := by
    intro z hz
    exact ((analyticOnNhd_classicalHillFrequencyPrimitive (z,a) (hsource' z hz)).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)).add analyticAt_const
  have hG : AnalyticOnNhd ℂ G (sphere (c : ℂ) rho) := by
    intro z hz
    exact (hB' (z^2) (hshell z hz)).comp (f := fun z : ℂ => z^2) (analyticAt_id.pow 2)
  have hsq' (z : ℂ) (hz : z ∈ sphere (c : ℂ) rho) : G z^2 = F z^2 := by
    have hz' := hshell z hz
    have hb := (hsq (z^2) (by simpa only [E,R,c,ofReal_mul,ofReal_natCast] using hz')).2
    exact hb.trans (hmatch (z^2) (by
      simpa only [classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using
        ball_subset_closedBall hz'.1) (hsource' z hz))
  have hgne (z : ℂ) (hz : z ∈ sphere (c : ℂ) rho) : G z ≠ 0 :=
    (hsq (z^2) (by simpa only [E,R,c,ofReal_mul,ofReal_natCast] using hshell z hz)).1
  obtain ⟨k,hk,hFG⟩ := exists_fixed_sign_of_sq_eq_on_preconnected F G (sphere (c : ℂ) rho)
    (isPreconnected_sphere (by simp) _ _) hF.continuousOn hG.continuousOn
    (fun z hz => (hsq' z hz).symm) hgne
  have hint : (∮ z in C((c : ℂ),rho), F z^m*(2*z)) =
      k^m*(∮ z in C((c : ℂ),rho), B (z^2)^m*(2*z)) := by
    calc
      _ = ∮ z in C((c : ℂ),rho), k^m*(B (z^2)^m*(2*z)) := by
        apply circleIntegral.integral_congr hrho.le
        intro z hz
        change F z^m*(2*z) = k^m*(B (z^2)^m*(2*z))
        rw [hFG z hz,mul_pow]
        dsimp only [G]
        ring
      _ = _ := circleIntegral.integral_const_mul _ _ _ _
  have hcut : AnalyticOnNhd ℂ (fun z => B z^m)
      (closedBall E (3*c*rho) \ closedBall E (c*rho)) := by
    intro z hz
    have hzlow : c*rho < ‖z-E‖ := by simpa only [mem_closedBall,dist_eq_norm,not_le] using hz.2
    have hzhigh : ‖z-E‖ ≤ 3*c*rho := by simpa only [mem_closedBall,dist_eq_norm] using hz.1
    have hzR : z ∈ ball E R := by rw [mem_ball,dist_eq_norm]; dsimp only [rho,R] at *; nlinarith
    have hzcut : z ∉ segment ℝ l u := by
      intro he
      have hh : ‖z-E‖ < R/8 := by simpa only [mem_ball,dist_eq_norm] using hseg he
      dsimp only [rho,R] at *
      nlinarith
    exact (hB' z ⟨hzR,hzcut⟩).pow m
  have hp := circleIntegral_square_pullback_eq_energy_circle (fun z => B z^m) c rho hc hrho hrhoc hcut
  refine ⟨k,hk,?_⟩
  rw [hmoment]
  have hcC : (Real.pi : ℂ)*(n : ℕ) = (c : ℂ) := by simp only [c,ofReal_mul,ofReal_natCast]
  rw [hcC]
  change (Real.pi : ℂ)⁻¹*(∮ z in C((c : ℂ),rho), F z^m*(2*z)) = _
  rw [hint,hp]
  have he : 2*c*rho = Real.pi*(n : ℕ)*r/2 := by dsimp only [c,rho]; ring
  rw [he]
  simp only [c,ofReal_mul,ofReal_natCast]
  ring


theorem classicalHill_moment_eq_signed_cut_moment
    (a : Curve ℂ) (n : ℕ+) (r : ℝ) (K B : ℂ → ℂ) (l u : ℂ)
    (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (hl : l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8))
    (hu : u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8))
    (hB : AnalyticOnNhd ℂ B
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hsq : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u,
      B z ≠ 0 ∧ B z^2 = K z)
    (hmatch : ∀ z ∈ classicalHillGapSquareDisc n r, (z,a) ∈ classicalHillContinuationDomain →
      K z = (classicalHillContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^2)
    (hsource : ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (r/4),
      (z^2,a) ∈ classicalHillContinuationDomain)
    (hmoment : classicalHillHighContourMoment n a =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),r/4),
        (classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi)^3*(2*z)) :
    ∃ k : ℂ, (k = 1 ∨ k = -1) ∧
      classicalHillHighContourMoment n a = k^3 *
        cubicMoment B (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/2) := by
  exact classicalHill_power_period_eq_signed_cut_period a n r K B l u 3
    (classicalHillHighContourMoment n a) hr hrpi hl hu hB hsq hmatch hsource hmoment

end NLS.KdV
