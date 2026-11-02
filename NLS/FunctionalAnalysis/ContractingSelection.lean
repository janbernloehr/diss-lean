import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-! Comparison and continuity of selected fixed points from a uniform local contraction. -/
noncomputable section
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E]

/-- Comparison needs the contraction bound only at the two actual fixed points. -/
theorem norm_sub_fixedPoints_le (F G : E → E) (u v : E) (K : ℝ) (hK : K < 1)
    (hu : F u = u) (hv : G v = v) (hLip : ‖F u-F v‖ ≤ K*‖u-v‖) :
    ‖u-v‖ ≤ ‖F v-G v‖/(1-K) := by
  have ht : ‖u-v‖ ≤ K*‖u-v‖+‖F v-G v‖ := by
    calc
      _ = ‖(F u-F v)+(F v-G v)‖ := by rw [hu, hv]; congr 1; abel
      _ ≤ ‖F u-F v‖+‖F v-G v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hLip le_rfl
  apply (le_div_iff₀ (sub_pos.mpr hK)).mpr
  nlinarith

/-- A selected fixed point is continuous when the contraction is uniform near
the parameter and the family is continuous at the fixed base vector. -/
theorem continuousAt_of_contracting_fixedPoints {X : Type*} [TopologicalSpace X]
    (F : X → E → E) (a : X → E) (x : X) (K : ℝ) (hK : K < 1)
    (hx : F x (a x) = a x)
    (hnear : ∀ᶠ y in 𝓝 x, F y (a y) = a y ∧
      ‖F y (a y)-F y (a x)‖ ≤ K*‖a y-a x‖)
    (hF : ContinuousAt (fun y => F y (a x)) x) : ContinuousAt a x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := (Metric.tendsto_nhds.mp hF.tendsto) (ε*(1-K))
    (mul_pos hε (sub_pos.mpr hK))
  filter_upwards [hnear, hsmall] with y hy herr
  rw [dist_eq_norm]
  apply (norm_sub_fixedPoints_le (F y) (F x) (a y) (a x) K hK hy.1 hx hy.2).trans_lt
  apply (div_lt_iff₀ (sub_pos.mpr hK)).mpr
  simpa only [dist_eq_norm] using herr

end NLS.FunctionalAnalysis
