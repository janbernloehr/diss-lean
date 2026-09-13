import NLS.ZakharovShabat.ResonantDeterminantBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Cauchy's derivative estimate and the branch-free root gap bound

A radius-`π/4` circle about every point of the refined disc remains in the
full strip. Cauchy's estimate bounds the diagonal derivative by `1/8`.
Two squared residual bounds then give the factor six without constructing
or choosing analytic square roots of the off-diagonal product.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- A quarter-spacing neighborhood of any refined-disc point stays within the strip. -/
theorem closedBall_refined_point_subset_strip (n : ℤ) (x : ℂ) (hx : x ∈ refinedResonantDisk n) :
    Metric.closedBall x (Real.pi/4) ⊆ resonantStrip n := by
  intro z hz
  apply closedBall_subset_resonantStrip n le_rfl
  apply Metric.mem_closedBall.mpr
  have hxc : dist x ((Real.pi : ℂ)*n) < Real.pi/4 := hx
  have hzx := Metric.mem_closedBall.mp hz
  exact (dist_triangle z x _).trans (by linarith)

/-- Cauchy's estimate gives the source derivative bound on the full refined disc. -/
theorem norm_deriv_le_on_refined_disk (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32) (x : ℂ) (hx : x ∈ refinedResonantDisk n) :
    ‖deriv a x‖ ≤ 1/8 := by
  have hball := closedBall_refined_point_subset_strip n x hx
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < Real.pi/4)
    (ha.differentiableOn.diffContOnCl_ball hball)
    (fun z hz => hb z (hball (Metric.sphere_subset_closedBall hz)))
  have he : (Real.pi/32)/(Real.pi/4) = (1/8 : ℝ) := by field_simp; ring
  exact h.trans_eq he

/-- The diagonal is `1/8`-Lipschitz between arbitrary complex points in the refined disc. -/
theorem norm_diagonal_sub_le_on_refined_disk (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n) :
    ‖a x-a y‖ ≤ (1/8 : ℝ)*‖x-y‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (ha z (refinedResonantDisk_subset_strip n hz)).differentiableAt)
    (norm_deriv_le_on_refined_disk n a ha hb) (convex_ball _ _) hy hx

/-- Two quadratic residual bounds and the diagonal Lipschitz estimate give the source factor six. -/
theorem norm_gap_sq_le_of_residual_bounds (c x y : ℂ) (a : ℂ → ℂ) (M : ℝ)
    (ha : ‖a x-a y‖ ≤ (1/8 : ℝ)*‖x-y‖)
    (hx : ‖x-c-a x‖^2 ≤ M) (hy : ‖y-c-a y‖^2 ≤ M) : ‖x-y‖^2 ≤ 6*M := by
  have he : x-y = (a x-a y) + ((x-c-a x)-(y-c-a y)) := by ring
  have ht : ‖x-y‖ ≤ (1/8 : ℝ)*‖x-y‖ + (‖x-c-a x‖ + ‖y-c-a y‖) := by
    calc
      _ = ‖(a x-a y) + ((x-c-a x)-(y-c-a y))‖ := congrArg norm he
      _ ≤ ‖a x-a y‖ + (‖x-c-a x‖ + ‖y-c-a y‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
      _ ≤ _ := add_le_add ha le_rfl
  have hlin : (7/8 : ℝ)*‖x-y‖ ≤ ‖x-c-a x‖+‖y-c-a y‖ := by linarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (7/8 : ℝ)*‖x-y‖) hlin
  have hM : 0 ≤ M := (sq_nonneg _).trans hx
  nlinarith [sq_nonneg (‖x-c-a x‖-‖y-c-a y‖)]

end NLS.ZakharovShabat
