import NLS.ComplexAnalysis.ComplexSegmentComplementConnected
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Analysis.Complex.CauchyIntegral

/-! An analytic extension of a derivative fills a disc cut by a
complex segment, while preserving EVERY value of the given primitive.
Collapsed segments are included. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_primitive_disc_cut_extension (f F g : ℂ → ℂ) (c l r : ℂ) (R : ℝ)
    (hgap : segment ℝ l r ⊆ ball c R) (hg : AnalyticOnNhd ℂ g (ball c R))
    (hF : ∀ z ∈ ball c R \ segment ℝ l r, HasDerivAt F (f z) z)
    (heq : EqOn f g (ball c R \ segment ℝ l r)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball c R) ∧
      EqOn H F (ball c R \ segment ℝ l r) ∧
      (∀ z ∈ ball c R, HasDerivAt H (g z) z) ∧
      ∀ a ∈ ball c R, Tendsto F (𝓝[ball c R \ segment ℝ l r] a) (𝓝 (H a)) := by
  have hclosed : IsClosed (segment ℝ l r) := by
    apply IsCompact.isClosed
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hconn := (isPathConnected_convex_complex_segment_complement_including_singleton (ball c R) l r
    isOpen_ball (convex_ball _ _) (hgap (left_mem_segment ℝ _ _))).isConnected.isPreconnected
  obtain ⟨G,hG⟩ := exists_primitive_on_convex g (ball c R) (convex_ball _ _) isOpen_ball hg.differentiableOn
  obtain ⟨C,hC⟩ := (isOpen_ball.sdiff hclosed).exists_eq_add_of_deriv_eq hconn
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG z hz.1).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).deriv.trans ((heq hz).trans (hG z hz.1).deriv.symm))
  have hH (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt (fun w => G w+C) (g z) z := (hG z hz).add_const C
  refine ⟨fun z => G z+C,
    (show DifferentiableOn ℂ (fun z => G z+C) (ball c R) from
      fun z hz => (hH z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball,
    fun z hz => (hC hz).symm,hH,?_⟩
  intro a ha
  apply ((hH a ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hC hz).symm

end NLS.ComplexAnalysis
