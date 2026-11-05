import NLS.ComplexAnalysis.DiscBounds
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Local Cauchy estimates inside an analytic closed disc -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_deriv_le_of_analytic_closedDisc_bound {f : ℂ → ℂ} (c : ℂ) {r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hrR : r < R) (B : ℝ)
    (hb : ∀ w ∈ closedBall c R, ‖f w‖ ≤ B) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv f z‖ ≤ B/(R-r) := by
  have hsub : closedBall z (R-r) ⊆ closedBall c R := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw hz ⊢
    exact (norm_sub_le_norm_sub_add_norm_sub w z c).trans
      ((add_le_add hw hz).trans_eq (by ring))
  have ha : AnalyticOnNhd ℂ f (closedBall z (R-r)) := hf.mono hsub
  have hd : DiffContOnCl ℂ f (ball z (R-r)) :=
    DiffContOnCl.mk_ball (ha.differentiableOn.mono ball_subset_closedBall) ha.continuousOn
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (sub_pos.mpr hrR) hd
  intro w hw
  exact hb w (hsub (sphere_subset_closedBall hw))

end NLS.ComplexAnalysis
