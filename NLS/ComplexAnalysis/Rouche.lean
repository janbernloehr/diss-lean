import NLS.ComplexAnalysis.ArgumentPrinciple
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Rouché's theorem for scalar analytic zero counts

A strict boundary perturbation keeps the ratio in the disc centered at one
with radius one. Its principal logarithm is a single-valued primitive of
the difference of logarithmic derivatives along the circle. The argument
principle then gives equality of the sums of analytic zero multiplicities.
-/

noncomputable section
open Metric
namespace NLS.ComplexAnalysis

/-- Strict relative perturbations are nonzero and their ratio admits the principal logarithm. -/
theorem rouche_ratio_mem_slitPlane {a b : ℂ} (h : ‖b-a‖ < ‖a‖) :
    a ≠ 0 ∧ b ≠ 0 ∧ b/a ∈ Complex.slitPlane := by
  have ha : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt h)
  have hb : b ≠ 0 := by
    intro hb
    simp [hb] at h
  refine ⟨ha,hb,?_⟩
  have he : b/a - 1 = (b-a)/a := by rw [sub_div, div_self ha]
  have hn : ‖b/a - 1‖ < 1 := by
    rw [he, norm_div, div_lt_one (norm_pos_iff.mpr ha)]
    exact h
  simpa only [add_sub_cancel] using Complex.mem_slitPlane_of_norm_lt_one hn

/-- A strict boundary perturbation preserves the logarithmic-derivative contour integral. -/
theorem circleIntegral_logDeriv_eq_of_boundary_lt {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (sphere c R))
    (hg : AnalyticOnNhd ℂ g (sphere c R))
    (h : ∀ z ∈ sphere c R, ‖g z-f z‖ < ‖f z‖) :
    (∮ z in C(c, R), logDeriv g z) = ∮ z in C(c, R), logDeriv f z := by
  have hn := fun z hz => rouche_ratio_mem_slitPlane (h z hz)
  have hi : (∮ z in C(c, R), logDeriv g z - logDeriv f z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
      (f := fun z => Complex.log (g z/f z))
    intro z hz
    have hdf := (hf z hz).differentiableAt
    have hdg := (hg z hz).differentiableAt
    have hd := ((hdg.div hdf (hn z hz).1).hasDerivAt.clog (hn z hz).2.2).hasDerivWithinAt (s := sphere c R)
    change HasDerivWithinAt (fun z => Complex.log (g z/f z))
      (logDeriv (fun z => g z/f z) z) (sphere c R) z at hd
    rwa [logDeriv_div z (hn z hz).2.1 (hn z hz).1 hdg hdf] at hd
  have hfi : CircleIntegrable (logDeriv f) c R := ContinuousOn.circleIntegrable hR
    (fun z hz => (analyticAt_logDeriv (hf z hz) (hn z hz).1).continuousAt.continuousWithinAt)
  have hgi : CircleIntegrable (logDeriv g) c R := ContinuousOn.circleIntegrable hR
    (fun z hz => (analyticAt_logDeriv (hg z hz) (hn z hz).2.1).continuousAt.continuousWithinAt)
  rw [circleIntegral.integral_sub hgi hfi] at hi
  exact sub_eq_zero.mp hi

/-- Rouché's theorem counts scalar zeros with their analytic multiplicities. -/
theorem analyticZeroCount_eq_of_boundary_lt {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (h : ∀ z ∈ sphere c R, ‖g z-f z‖ < ‖f z‖) :
    analyticZeroCount g (closedBall c R) = analyticZeroCount f (closedBall c R) := by
  have hn := fun z hz => rouche_ratio_mem_slitPlane (h z hz)
  have he := circleIntegral_logDeriv_eq_of_boundary_lt hR.le
    (hf.mono sphere_subset_closedBall) (hg.mono sphere_subset_closedBall) h
  rw [circleIntegral_logDeriv_eq_analyticZeroCount hR hg (fun z hz => (hn z hz).2.1),
    circleIntegral_logDeriv_eq_analyticZeroCount hR hf (fun z hz => (hn z hz).1)] at he
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  exact_mod_cast (mul_left_cancel₀ hc he)

end NLS.ComplexAnalysis
