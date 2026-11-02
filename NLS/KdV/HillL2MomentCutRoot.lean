import NLS.KdV.HillL2MomentRadius
import NLS.KdV.HillL2GapCutRoots
import Mathlib.Analysis.Normed.Module.Connected

/-! # Matching actual L2 periods to a cut-root circle

A connected energy circle fixes one sign for the whole integral. The
source period is therefore an actual cut-root period, without a choice
of signs on every component of the full cut complement.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2_power_period_eq_signed_cut_period
    (a : Coeff 2) (n : ℕ+) (c l u : ℂ) (R : ℝ) (K B : ℂ → ℂ) (m : ℕ) (P : ℂ)
    (hR : 0 < R) (hl : l ∈ ball c (R/32)) (hu : u ∈ ball c (R/32))
    (hB : AnalyticOnNhd ℂ B (ball c R \ segment ℝ l u))
    (hsq : ∀ z ∈ ball c R \ segment ℝ l u, B z ≠ 0 ∧ B z^2 = K z)
    (hmatch : ∀ z ∈ closedBall c R, (z,a) ∈ hillL2ContinuationDomain →
      K z = (hillL2ContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^2)
    (hsource : ∀ z ∈ sphere c (R/4), (z,a) ∈ hillL2ContinuationDomain)
    (hperiod : P = (Real.pi : ℂ)⁻¹ * ∮ z in C(c,R/4),
      (hillL2ContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m) :
    ∃ k : ℂ, (k = 1 ∨ k = -1) ∧
      P = k^m*((Real.pi : ℂ)⁻¹*∮ z in C(c,R/4), B z^m) := by
  let F : ℂ → ℂ := fun z => hillL2ContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi
  have hseg : segment ℝ l u ⊆ ball c (R/32) := (convex_ball _ _).segment_subset hl hu
  have hcircle (z : ℂ) (hz : z ∈ sphere c (R/4)) : z ∈ ball c R \ segment ℝ l u := by
    refine ⟨sphere_subset_ball (by linarith) hz,?_⟩
    intro hs
    have hnear := mem_ball.mp (hseg hs)
    have he := mem_sphere.mp hz
    linarith
  have hF : AnalyticOnNhd ℂ F (sphere c (R/4)) := by
    intro z hz
    exact ((analyticOnNhd_hillL2ContinuedPrimitive _ (hsource z hz)).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)).add analyticAt_const
  have hBs : AnalyticOnNhd ℂ B (sphere c (R/4)) := hB.mono hcircle
  have heq (z : ℂ) (hz : z ∈ sphere c (R/4)) : F z^2 = B z^2 := by
    exact (hmatch z (closedBall_subset_closedBall (by linarith : R/4 ≤ R)
      (sphere_subset_closedBall hz)) (hsource z hz)).symm.trans (hsq z (hcircle z hz)).2.symm
  obtain ⟨k,hk,hFB⟩ := exists_fixed_sign_of_sq_eq_on_preconnected F B (sphere c (R/4))
    (isPreconnected_sphere (by simp) _ _) hF.continuousOn hBs.continuousOn heq
    (fun z hz => (hsq z (hcircle z hz)).1)
  refine ⟨k,hk,?_⟩
  rw [hperiod]
  change (Real.pi : ℂ)⁻¹*(∮ z in C(c,R/4), F z^m) = _
  have hi : (∮ z in C(c,R/4), F z^m) = k^m*(∮ z in C(c,R/4), B z^m) := by
    calc
      _ = ∮ z in C(c,R/4), k^m*B z^m := by
        apply circleIntegral.integral_congr (by positivity)
        intro z hz
        change F z^m = k^m*B z^m
        rw [hFB z hz,mul_pow]
      _ = _ := circleIntegral.integral_const_mul _ _ _ _
  rw [hi]
  ring

end NLS.KdV
