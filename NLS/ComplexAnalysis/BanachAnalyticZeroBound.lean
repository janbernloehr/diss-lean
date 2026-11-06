import NLS.ComplexAnalysis.BanachTaylorBounds
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.ComplexAnalysis



variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A bounded analytic map vanishing at the origin has a uniform linear
norm bound on a fixed fraction of the original ball. -/
theorem norm_le_mul_norm_of_analytic_zero_ball_bound
    (f : E → F) (δ M : ℝ) (hδ : 0<δ)
    (hf : AnalyticOnNhd ℂ f (ball 0 δ)) (hzero : f 0=0)
    (hb : ∀ x∈ball 0 δ, ‖f x‖≤M) (x : E) (hx : x∈ball 0 (δ/4)) :
    ‖f x‖≤(8*M/δ)*‖x‖ := by
  let r := δ/4
  have hr : 0<r := by dsimp only [r];positivity
  have hsub : ball (0 : E) (r+r) ⊆ ball 0 δ := ball_subset_ball (by dsimp only [r];linarith)
  have hsub' : ball (0 : E) r ⊆ ball 0 δ := ball_subset_ball (by dsimp only [r];linarith)
  have hAt (w : E) (hw : w∈ball 0 r) : DifferentiableAt ℂ f w :=
    (hf w (hsub' hw)).differentiableAt
  have hder (w : E) (hw : w∈ball 0 r) : ‖fderiv ℂ f w‖≤8*M/δ := by
    exact (norm_fderiv_le_of_ball_bound f 0 w r r M hr
      (hf.differentiableOn.mono hsub) (fun z hz => hb z (hsub hz)) hw).trans_eq
        (by dsimp only [r];field_simp;ring)
  have hh := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_fderiv_le
    hAt hder (mem_ball_self hr) hx
  simpa only [hzero,sub_zero] using hh

end NLS.ComplexAnalysis
