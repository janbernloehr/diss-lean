import Mathlib.Analysis.Complex.RemovableSingularity

/-! # A bounded holomorphic puncture has zero circle integral -/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem circleIntegral_eq_zero_of_bounded_puncture (f : ℂ → ℂ) (c : ℂ) (r R M : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (ball c R \ {c}))
    (hb : ∀ z ∈ ball c R \ {c}, ‖f z‖ ≤ M) :
    (∮ z in C(c, r), f z) = 0 := by
  have hR : 0 < R := hr.trans hrR
  let g := Function.update f c ((𝓝[≠] c).limUnder f)
  have hg : DifferentiableOn ℂ g (ball c R) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove
      (isOpen_ball.mem_nhds (mem_ball_self hR)) hf.differentiableOn
      ⟨M, by rintro _ ⟨z, hz, rfl⟩; exact hb z hz⟩
  have hga := hg.analyticOnNhd isOpen_ball
  calc
    _ = ∮ z in C(c, r), g z := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      have hne : z ≠ c := by
        intro he
        have hd := mem_sphere.mp hz
        rw [he, dist_self] at hd
        linarith
      exact (Function.update_of_ne hne _ _).symm
    _ = 0 := circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
      (hga.mono (closedBall_subset_ball hrR)).continuousOn
      (fun z hz => (hga z (closedBall_subset_ball hrR (ball_subset_closedBall hz.1))).differentiableAt)

end NLS.ComplexAnalysis
