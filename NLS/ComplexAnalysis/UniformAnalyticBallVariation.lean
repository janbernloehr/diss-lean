import NLS.ComplexAnalysis.BanachTaylorBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform variation of bounded holomorphic maps on a common Banach ball -/
noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem norm_sub_base_le_of_analytic_ball_bound (f : E → F) (c : E) {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball c R)) (hb : ∀ y ∈ ball c R, ‖f y‖ ≤ M)
    {x : E} (hx : x ∈ ball c (R/2)) : ‖f x-f c‖ ≤ (4*M/R)*‖x-c‖ := by
  have hAt (w : E) (hw : w ∈ ball c (R/2)) : DifferentiableAt ℂ f w :=
    (hf w (ball_subset_ball (by linarith : R/2 ≤ R) hw)).differentiableAt
  have hder (w : E) (hw : w ∈ ball c (R/2)) : ‖fderiv ℂ f w‖ ≤ 4*M/R := by
    have he : R/2+R/2 = R := by ring
    have h := norm_fderiv_le_of_ball_bound f c w (R/2) (R/2) M (by positivity)
      (by rw [he]; exact hf.differentiableOn) (by rw [he]; exact hb) hw
    apply h.trans_eq
    ring
  exact (convex_ball c (R/2)).norm_image_sub_le_of_norm_fderiv_le hAt hder
    (mem_ball_self (by positivity)) hx

end NLS.ComplexAnalysis
