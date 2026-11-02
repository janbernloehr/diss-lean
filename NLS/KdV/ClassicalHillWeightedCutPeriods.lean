import NLS.KdV.ClassicalHillGapCutRoots
import NLS.KdV.ClassicalHillAnnulusCoverage
import NLS.KdV.ClassicalHighContourMoments
import NLS.ComplexAnalysis.SquaredCircleHomotopy
import Mathlib.Analysis.Normed.Module.Connected

/-! # Weighted actual Hill powers on cut-root energy circles

A connected frequency circle fixes the actual primitive sign. The exact
quadratic contour homotopy retains an analytic energy weight, which may
have poles inside the circle. The Jacobian is exactly 2*z.
-/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem classicalHill_frequency_weighted_power_radius_independence
    (W : ℂ → ℂ) (k : ℕ+) (m : ℕ) (q : Curve ℂ)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (hcover : ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      r ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖ → (z^2,q) ∈ classicalHillContinuationDomain)
    (hW : ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) \
      ball ((Real.pi : ℂ)*(k : ℕ)) r, AnalyticAt ℂ W (z^2)) :
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*W (z^2)*(2*z)) =
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),r),
        (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*W (z^2)*(2*z) := by
  let c : ℂ := (Real.pi : ℂ)*(k : ℕ)
  let f (z : ℂ) := (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*W (z^2)*(2*z)
  have hf : AnalyticOnNhd ℂ f (closedBall c (Real.pi/4) \ ball c r) := by
    intro z hz
    have ht := hcover z hz.1 (by simpa only [mem_ball,dist_eq_norm,not_lt] using hz.2)
    have hF := (analyticOnNhd_classicalHillContinuedPrimitive (z^2,q) ht).comp
      (f := fun z : ℂ => (z^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)
    have hWz := (hW z hz).comp (f := fun z : ℂ => z^2) (analyticAt_id.pow 2)
    exact (((hF.add analyticAt_const).pow m).mul hWz).mul (analyticAt_const.mul analyticAt_id)
  exact circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrpi countable_empty hf.continuousOn
    (fun z hz => (hf z ⟨ball_subset_closedBall hz.1.1,fun hh => hz.1.2 (ball_subset_closedBall hh)⟩).differentiableAt)

theorem classicalHill_weighted_power_period_eq_signed_cut_period
    (a : Curve ℂ) (n : ℕ+) (r : ℝ) (K B : ℂ → ℂ) (l u : ℂ) (m : ℕ) (W : ℂ → ℂ)
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
    (hW : AnalyticOnNhd ℂ W
      (closedBall (((Real.pi : ℂ)*(n : ℕ))^2) (3*(Real.pi*(n : ℕ))*(r/4)) \
        closedBall (((Real.pi : ℂ)*(n : ℕ))^2) ((Real.pi*(n : ℕ))*(r/4)))) :
    ∃ k : ℂ, (k = 1 ∨ k = -1) ∧
      (∮ z in C((Real.pi : ℂ)*(n : ℕ),r/4),
        (classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m*W (z^2)*(2*z)) =
      k^m*(∮ z in C((((Real.pi : ℂ)*(n : ℕ))^2),Real.pi*(n : ℕ)*r/2), B z^m*W z) := by
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
  have hint : (∮ z in C((c : ℂ),rho), F z^m*W (z^2)*(2*z)) =
      k^m*(∮ z in C((c : ℂ),rho), B (z^2)^m*W (z^2)*(2*z)) := by
    calc
      _ = ∮ z in C((c : ℂ),rho), k^m*(B (z^2)^m*W (z^2)*(2*z)) := by
        apply circleIntegral.integral_congr hrho.le
        intro z hz
        change F z^m*W (z^2)*(2*z) = k^m*(B (z^2)^m*W (z^2)*(2*z))
        rw [hFG z hz,mul_pow]
        dsimp only [G]
        ring
      _ = _ := circleIntegral.integral_const_mul _ _ _ _
  have hcut : AnalyticOnNhd ℂ (fun z => B z^m*W z)
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
    have hWz := hW z (by simpa only [E,c,rho,ofReal_mul,ofReal_natCast] using hz)
    exact ((hB' z ⟨hzR,hzcut⟩).pow m).mul hWz
  have hp := circleIntegral_square_pullback_eq_energy_circle (fun z => B z^m*W z) c rho hc hrho hrhoc hcut
  refine ⟨k,hk,?_⟩
  have hcC : (Real.pi : ℂ)*(n : ℕ) = (c : ℂ) := by simp only [c,ofReal_mul,ofReal_natCast]
  rw [hcC]
  change (∮ z in C((c : ℂ),rho), F z^m*W (z^2)*(2*z)) = _
  rw [hint,hp]
  have he : 2*c*rho = Real.pi*(n : ℕ)*r/2 := by dsimp only [c,rho]; ring
  rw [he]


end NLS.KdV
