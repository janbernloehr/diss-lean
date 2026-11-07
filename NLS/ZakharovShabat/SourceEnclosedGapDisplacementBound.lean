import NLS.ZakharovShabat.SourceStandardRootGapSideSource
import NLS.ZakharovShabat.SourcePeriodicGapSummability

/-! An enclosing disc controls midpoint displacement and half-gap at
ANY terminal, independently of the gap length or its physical sheet. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_sub_midpoint_add_halfGap_le_of_enclosed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c z : ℂ) (r : ℝ)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (hz : z ∈ closedBall c r) :
    ‖z-sourceStandardRootMidpoint hp hp1 ψ m‖+
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤ 3*r := by
  have hμ := mem_closedBall.mp hz
  have hτ := (mem_ball.mp (hgap (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))).le
  have hl := (mem_ball.mp (hgap (left_mem_segment ℝ _ _))).le
  have hr := (mem_ball.mp (hgap (right_mem_segment ℝ _ _))).le
  have hμτ := dist_triangle_right z (sourceStandardRootMidpoint hp hp1 ψ m) c
  have hgap' := dist_triangle_right
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) m)
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) m) c
  rw [dist_eq_norm] at hμτ hgap'
  simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
  change _ ≤ _ at hτ
  linarith

end NLS.ZakharovShabat
