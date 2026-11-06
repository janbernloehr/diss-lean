import NLS.KdV.ActionHamiltonianMomentAlgebra
import NLS.KdV.ClassicalHillHighContourActions
import NLS.KdV.ClassicalHillGapQuotientAsymptotics
import NLS.ComplexAnalysis.QuadraticRootContourPeriod
import NLS.ComplexAnalysis.QuadraticRootBounds
import NLS.ComplexAnalysis.AnalyticCutContour

/-! # Quantitative gap comparison for the actual high Arnold periods

The oriented endpoint-root period fixes the free action coefficient.
A unit root close to i/(2*n*pi) makes the action period comparable to
the squared actual gap divided by n, including complex perturbations.
Global Birkhoff identification and action-space descent remain separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem norm_endpointRoot_unit_action_sub_le
    (l u : ℂ) (H : ℂ → ℂ) (c epsilon : ℝ) (hc : 0 < c)
    (hlu : l ≠ u) (hH : ContinuousOn H (sphere ((l+u)/2) ‖l-u‖))
    (hclose : ∀ z ∈ sphere ((l+u)/2) ‖l-u‖,
      ‖H z-I/(2*(c : ℂ))‖ ≤ epsilon/(2*c)) :
    ‖primitiveAction (fun z => endpointRoot l u z*H z) ((l+u)/2) ‖l-u‖-
        (l-u)^2/(8*(c : ℂ))‖ ≤ 3*epsilon*‖l-u‖^2/(2*c) := by
  let gamma : ℝ := ‖l-u‖
  let w : ℂ := I/(2*(c : ℂ))
  have hgamma : 0 < gamma := norm_pos_iff.mpr (sub_ne_zero.mpr hlu)
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hseg : segment ℝ l u ⊆ ball ((l+u)/2) gamma := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball,dist_eq_norm,show l-(l+u)/2 = (l-u)/2 by ring,norm_div]
      norm_num
      change gamma/2 < gamma
      linarith
    · rw [mem_ball,dist_eq_norm,show u-(l+u)/2 = (u-l)/2 by ring,norm_div,norm_sub_rev u l]
      norm_num
      change gamma/2 < gamma
      linarith
  have hcircle (z : ℂ) (hz : z ∈ sphere ((l+u)/2) gamma) : z ∉ segment ℝ l u := by
    intro hh
    exact sphere_disjoint_ball.le_bot ⟨hz,hseg hh⟩
  have hroot : ContinuousOn (endpointRoot l u) (sphere ((l+u)/2) gamma) := by
    intro z hz
    exact (analyticOnNhd_endpointRoot l u z (hcircle z hz)).continuousAt.continuousWithinAt
  have hrootnorm (z : ℂ) (hz : z ∈ sphere ((l+u)/2) gamma) : ‖endpointRoot l u z‖ ≤ 3*gamma/2 := by
    have hsq : endpointRoot l u z^2 = (z-(l+u)/2)^2-(l-u)^2/4 := by
      rw [endpointRoot_sq l u z (hcircle z hz)]
      ring
    have hh := norm_le_of_sq_eq_gap_polynomial _ (z-(l+u)/2) (l-u) hsq
    have he : ‖z-(l+u)/2‖ = gamma := by simpa only [mem_sphere,dist_eq_norm] using hz
    rw [he] at hh
    change ‖endpointRoot l u z‖ ≤ 3*gamma/2
    dsimp only [gamma] at *
    linarith
  have hmodel : primitiveAction (fun z => endpointRoot l u z*w) ((l+u)/2) gamma =
      (l-u)^2/(8*(c : ℂ)) := by
    unfold primitiveAction
    have he : (fun z => endpointRoot l u z*w) = fun z => w*endpointRoot l u z := by funext z; ring
    rw [he,circleIntegral.integral_const_mul,circleIntegral_endpointRoot l u hlu]
    dsimp only [w]
    field_simp [Real.pi_ne_zero,hcC]
    simp only [I_sq]
    ring
  have hi : CircleIntegrable (fun z => endpointRoot l u z*H z) ((l+u)/2) gamma :=
    (hroot.mul hH).circleIntegrable hgamma.le
  have hi0 : CircleIntegrable (fun z => endpointRoot l u z*w) ((l+u)/2) gamma :=
    (hroot.mul continuousOn_const).circleIntegrable hgamma.le
  rw [← hmodel,← primitiveAction_sub _ _ _ _ hi hi0]
  have hb := norm_primitiveAction_le
    (fun z => endpointRoot l u z*H z-endpointRoot l u z*w) ((l+u)/2) gamma
    ((3*gamma/2)*(epsilon/(2*c))) hgamma.le (by
      intro z hz
      rw [show endpointRoot l u z*H z-endpointRoot l u z*w = endpointRoot l u z*(H z-w) by ring,norm_mul]
      exact mul_le_mul (hrootnorm z hz) (hclose z hz) (norm_nonneg _) (by positivity))
  calc
    _ ≤ 2*gamma*((3*gamma/2)*(epsilon/(2*c))) := hb
    _ = 3*epsilon*‖l-u‖^2/(2*c) := by dsimp only [gamma]; ring

theorem norm_endpointRoot_unit_action_lower
    (l u : ℂ) (H : ℂ → ℂ) (c epsilon : ℝ) (hc : 0 < c)
    (hepsilon32 : epsilon ≤ 1/32) (hlu : l ≠ u)
    (hH : ContinuousOn H (sphere ((l+u)/2) ‖l-u‖))
    (hclose : ∀ z ∈ sphere ((l+u)/2) ‖l-u‖,
      ‖H z-I/(2*(c : ℂ))‖ ≤ epsilon/(2*c)) :
    ‖l-u‖^2/(16*c) ≤ ‖primitiveAction (fun z => endpointRoot l u z*H z) ((l+u)/2) ‖l-u‖‖ := by
  have hb := norm_endpointRoot_unit_action_sub_le l u H c epsilon hc hlu hH hclose
  let S : ℝ := ‖l-u‖^2/c
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hmodelnorm : ‖(l-u)^2/(8*(c : ℂ))‖ = S/8 := by
    simp only [norm_div,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hc]
    dsimp only [S]
    ring
  have herr : 3*epsilon*‖l-u‖^2/(2*c) ≤ (3/64)*S := by
    calc
      _ = (3*epsilon/2)*S := by dsimp only [S]; ring
      _ ≤ (3/64)*S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hh := norm_sub_norm_le ((l-u)^2/(8*(c : ℂ)))
    (primitiveAction (fun z => endpointRoot l u z*H z) ((l+u)/2) ‖l-u‖)
  rw [norm_sub_rev ((l-u)^2/(8*(c : ℂ)))
    (primitiveAction (fun z => endpointRoot l u z*H z) ((l+u)/2) ‖l-u‖),hmodelnorm] at hh
  have he : ‖l-u‖^2/(16*c) = S/16 := by dsimp only [S]; ring
  rw [he]
  linarith

theorem primitiveAction_cut_eq_gap_circle
    (B : ℂ → ℂ) (c l u : ℂ) (R : ℝ) (hR : 0 < R)
    (hl : l ∈ ball c (R/8)) (hu : u ∈ ball c (R/8)) (hlu : l ≠ u)
    (hB : AnalyticOnNhd ℂ B (ball c R \ segment ℝ l u)) :
    primitiveAction B c (R/2) = primitiveAction B ((l+u)/2) ‖l-u‖ := by
  have hgamma : 0 < ‖l-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hlu)
  have hl' : ‖l-c‖ < R/8 := by simpa only [mem_ball,dist_eq_norm] using hl
  have hu' : ‖u-c‖ < R/8 := by simpa only [mem_ball,dist_eq_norm] using hu
  have hgap : ‖l-u‖ ≤ R/4 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub l c u
    rw [norm_sub_rev c u] at hh
    linarith
  have hmid := norm_complex_midpoint_sub_le l u c (R/8) hl'.le hu'.le
  have hnest : closedBall ((l+u)/2) ‖l-u‖ ⊆ closedBall c (R/2) := by
    intro z hz
    have hz' : ‖z-(l+u)/2‖ ≤ ‖l-u‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hh := norm_sub_le_norm_sub_add_norm_sub z ((l+u)/2) c
    have hh' : ‖z-c‖ ≤ R/2 := by linarith
    simpa only [mem_closedBall,dist_eq_norm] using hh'
  have hseginner : segment ℝ l u ⊆ ball ((l+u)/2) ‖l-u‖ := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball,dist_eq_norm,show l-(l+u)/2 = (l-u)/2 by ring,norm_div]
      norm_num
      exact sub_ne_zero.mpr hlu
    · rw [mem_ball,dist_eq_norm,show u-(l+u)/2 = (u-l)/2 by ring,norm_div,norm_sub_rev u l]
      norm_num
      exact sub_ne_zero.mpr hlu
  have hsegouter : segment ℝ l u ⊆ ball c (R/2) := (convex_ball _ _).segment_subset
    (ball_subset_ball (by linarith : R/8 ≤ R/2) hl)
    (ball_subset_ball (by linarith : R/8 ≤ R/2) hu)
  have heq := circleIntegral_eq_of_analytic_cut_nestedCircles B (ball c R) (segment ℝ l u) hB
    ((l+u)/2) c ‖l-u‖ (R/2) hgamma (by positivity) hseginner hsegouter hnest
    (closedBall_subset_ball (by linarith))
  exact congrArg (fun z : ℂ => -(Real.pi : ℂ)⁻¹*z) heq.symm

end NLS.KdV
