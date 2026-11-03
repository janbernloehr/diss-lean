import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.Normed.Field.Basic

/-! # Multiplying a bounded phase through its collapsed radius

A bounded angular factor need only be continuous off the zero set of a
continuous amplitude. Their product is continuous across the whole zero
set. This retains the original open-angle domain without assuming that
an angle has a continuous value at a collapsed action.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
variable {X : Type*} [PseudoMetricSpace X]

theorem continuous_mul_bounded_phase (W Q : X → ℂ) (hW : Continuous W)
    (hQ : ContinuousOn Q {x | W x ≠ 0}) (hbound : ∀ x, ‖Q x‖ ≤ 1) :
    Continuous (fun x => W x*Q x) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases ha : W a = 0
  · rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hclose⟩ := (Metric.continuousAt_iff.mp hW.continuousAt) ε hε
    refine ⟨δ,hδ,fun x hx => ?_⟩
    have hsmall : ‖W x‖ < ε := by simpa only [ha,dist_zero_right] using hclose hx
    rw [ha,zero_mul,dist_zero_right,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hbound x)).trans_lt hsmall
  · exact hW.continuousAt.mul (hQ.continuousAt ((isClosed_eq hW continuous_const).isOpen_compl.mem_nhds ha))

end NLS.ComplexAnalysis
