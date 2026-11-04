import NLS.ComplexAnalysis.TwoZeroDeflation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



theorem norm_analytic_unit_ratio_sub_one_le_on_disc
    (F F₀ P P₀ Q Q₀ : ℂ → ℂ) (c : ℂ) (R δ η : ℝ)
    (hR : 0 < R) (hη1 : η < 1)
    (hQ : AnalyticOnNhd ℂ Q (closedBall c R))
    (hQ₀ : AnalyticOnNhd ℂ Q₀ (closedBall c R))
    (hQ₀n : ∀ z ∈ closedBall c R, Q₀ z ≠ 0)
    (hP₀n : ∀ z ∈ sphere c R, P₀ z ≠ 0)
    (hF : ∀ z ∈ sphere c R, F z=P z*Q z)
    (hF₀ : ∀ z ∈ sphere c R, F₀ z=P₀ z*Q₀ z)
    (herror : ∀ z ∈ sphere c R, ‖F z/F₀ z-1‖ ≤ δ)
    (hpoly : ∀ z ∈ sphere c R, ‖P z/P₀ z-1‖ ≤ η) :
    ∀ z ∈ closedBall c R, ‖Q z/Q₀ z-1‖ ≤ (δ+η)/(1-η) := by
  let g : ℂ → ℂ := fun z => Q z/Q₀ z-1
  have hg : AnalyticOnNhd ℂ g (closedBall c R) := by
    intro z hz
    exact ((hQ z hz).div (hQ₀ z hz) (hQ₀n z hz)).sub analyticAt_const
  have hdc : DiffContOnCl ℂ g (ball c R) := by
    refine ⟨fun z hz => (hg z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt,?_⟩
    rw [closure_ball c hR.ne']
    exact hg.continuousOn
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
  · intro w hw
    rw [frontier_ball c hR.ne'] at hw
    have hq0 := hQ₀n w (sphere_subset_closedBall hw)
    have hp0 := hP₀n w hw
    have hid : g w*(P w/P₀ w) = (F w/F₀ w-1)-(P w/P₀ w-1) := by
      rw [hF w hw,hF₀ w hw]
      dsimp only [g]
      field_simp
      ring
    have hlo : 1-η ≤ ‖P w/P₀ w‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) (P w/P₀ w)
      rw [norm_one,norm_sub_rev] at hh
      linarith [hpoly w hw]
    have hm : ‖g w‖*(1-η) ≤ δ+η := by
      calc
        _ ≤ ‖g w‖*‖P w/P₀ w‖ := mul_le_mul_of_nonneg_left hlo (norm_nonneg _)
        _ = ‖(F w/F₀ w-1)-(P w/P₀ w-1)‖ := by rw [← norm_mul,hid]
        _ ≤ ‖F w/F₀ w-1‖+‖P w/P₀ w-1‖ := norm_sub_le _ _
        _ ≤ δ+η := add_le_add (herror w hw) (hpoly w hw)
    exact (le_div_iff₀ (by linarith : 0 < 1-η)).mpr hm
  · rw [closure_ball c hR.ne']
    exact hz

end NLS.ComplexAnalysis
