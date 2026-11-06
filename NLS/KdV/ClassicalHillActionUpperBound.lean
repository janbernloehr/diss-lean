import NLS.KdV.ActionHamiltonianMomentAlgebra
import NLS.KdV.ClassicalHillActionGapBounds

/-! # Quadratic upper bounds for cut-root Arnold periods

Deformation to the actual gap circle supplies one gap factor from its
radius and one from the primitive. The collapsed case is analytic across
the repeated root and has zero period.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem norm_primitiveAction_cut_le_gap
    (B : ℂ → ℂ) (c l u : ℂ) (R A m : ℝ) (hR : 0 < R)
    (hl : l ∈ ball c (R/8)) (hu : u ∈ ball c (R/8))
    (hB : AnalyticOnNhd ℂ B (ball c R \ segment ℝ l u))
    (hcollapsed : l = u → AnalyticOnNhd ℂ B (ball c R))
    (hbound : ∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u,
      ‖B z‖ ≤ A*‖l-u‖/m) :
    ‖primitiveAction B c (R/2)‖ ≤ 2*A*‖l-u‖^2/m := by
  by_cases he : l = u
  · have hz := primitiveAction_eq_zero_of_analyticOnNhd B c (R/2) (by positivity)
      ((hcollapsed he).mono (closedBall_subset_ball (by linarith)))
    simp only [hz,norm_zero,he,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_div,le_refl]
  have hgamma : 0 < ‖l-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hseg : segment ℝ l u ⊆ ball ((l+u)/2) ‖l-u‖ := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball,dist_eq_norm,show l-(l+u)/2 = (l-u)/2 by ring,norm_div]
      norm_num
      exact sub_ne_zero.mpr he
    · rw [mem_ball,dist_eq_norm,show u-(l+u)/2 = (u-l)/2 by ring,norm_div,norm_sub_rev u l]
      norm_num
      exact sub_ne_zero.mpr he
  rw [primitiveAction_cut_eq_gap_circle B c l u R hR hl hu he hB]
  have hb := norm_primitiveAction_le B ((l+u)/2) ‖l-u‖ (A*‖l-u‖/m) hgamma.le (by
    intro z hz
    apply hbound z
    refine ⟨sphere_subset_closedBall hz,?_⟩
    intro hs
    exact sphere_disjoint_ball.le_bot ⟨hz,hseg hs⟩)
  calc
    _ ≤ 2*‖l-u‖*(A*‖l-u‖/m) := hb
    _ = 2*A*‖l-u‖^2/m := by ring

end NLS.KdV
