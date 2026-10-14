import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Basic

/-! # A connected set cannot leave a ball without meeting its sphere -/

open Set Metric
namespace NLS.ComplexAnalysis

/-- One point inside a ball and avoidance of its sphere force an entire
preconnected set to remain inside. No parametrization is required. -/
theorem subset_ball_of_isPreconnected_of_disjoint_sphere
    {X : Type*} [PseudoMetricSpace X] {S : Set X} (hS : IsPreconnected S)
    (c : X) (r : ℝ) (havoid : Disjoint S (sphere c r))
    (hinside : (S ∩ ball c r).Nonempty) : S ⊆ ball c r := by
  intro z hz
  change dist z c < r
  apply hS.gt_of_ne (f := fun w => dist w c) (b := r) (x := z)
    (continuous_id.dist continuous_const).continuousOn
  · intro w hw he
    exact Set.disjoint_left.mp havoid hw (mem_sphere.mpr he)
  · obtain ⟨w,hw,hin⟩ := hinside
    exact ⟨w,hw,mem_ball.mp hin⟩
  · exact hz

end NLS.ComplexAnalysis
