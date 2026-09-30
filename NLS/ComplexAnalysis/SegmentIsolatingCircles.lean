import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! # Nested circles around a segment in an open disc -/

noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis

/-- A closed segment inside an open disc admits a smaller enclosing
circle and a strictly larger collar circle, both inside that disc. -/
theorem exists_nested_radii_of_segment_subset_ball (a b c : ℂ) (T : ℝ)
    (hseg : segment ℝ a b ⊆ ball c T) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ R < T ∧ segment ℝ a b ⊆ ball c r := by
  let A := max (dist a c) (dist b c)
  have hA : 0 ≤ A := (dist_nonneg : 0 ≤ dist a c).trans (le_max_left _ _)
  have hAT : A < T := max_lt
    (mem_ball.mp (hseg (left_mem_segment ℝ a b)))
    (mem_ball.mp (hseg (right_mem_segment ℝ a b)))
  let r := (A+T)/2
  let R := (r+T)/2
  have hAr : A < r := by dsimp [r]; linarith
  have hrT : r < T := by dsimp [r]; linarith
  refine ⟨r,R,by linarith,?_,?_,?_⟩
  · dsimp [R]; linarith
  · dsimp [R]; linarith
  · have hclosed : segment ℝ a b ⊆ closedBall c A :=
      (convex_closedBall c A).segment_subset
        (mem_closedBall.mpr (le_max_left _ _))
        (mem_closedBall.mpr (le_max_right _ _))
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp (hclosed hz)).trans_lt hAr)

end NLS.ComplexAnalysis
