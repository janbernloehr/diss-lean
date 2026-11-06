import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import Mathlib.Analysis.Complex.AbsMax

/-! # Endpoint-root and holomorphic quotient bounds on an enclosing disc -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_endpointRoot_le_twice_radius (a b c z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (ha : a ∈ closedBall c R) (hb : b ∈ closedBall c R) (hz : z ∈ sphere c R)
    (hcut : z ∉ segment ℝ a b) : ‖endpointRoot a b z‖ ≤ 2*R := by
  have hza : ‖z-a‖ ≤ 2*R := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z c a
    rw [norm_sub_rev c a] at ht
    have hzc : ‖z-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hz
    have hac : ‖a-c‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using ha
    linarith
  have hzb : ‖z-b‖ ≤ 2*R := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z c b
    rw [norm_sub_rev c b] at ht
    have hzc : ‖z-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hz
    have hbc : ‖b-c‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hb
    linarith
  have hs := congrArg norm (endpointRoot_sq a b z hcut)
  rw [norm_pow,norm_mul] at hs
  have hp := mul_le_mul hza hzb (norm_nonneg _) (by positivity : 0 ≤ 2*R)
  nlinarith [norm_nonneg (endpointRoot a b z)]

theorem norm_le_of_analytic_closedDisc_sphere_bound {f : ℂ → ℂ} (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (M : ℝ)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ closedBall c R) : ‖f z‖ ≤ M := by
  have hd : DifferentiableOn ℂ f (closure (ball c R)) := by
    rw [closure_ball c hR.ne']
    exact hf.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := c) (r := R)) hd.diffContOnCl
  · intro w hw
    rw [frontier_ball _ hR.ne'] at hw
    exact hb w hw
  · rw [closure_ball c hR.ne']
    exact hz

end NLS.ComplexAnalysis
