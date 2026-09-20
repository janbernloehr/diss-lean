import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax

/-!
# Value and derivative bounds from a circle

Maximum modulus fills a boundary bound throughout the closed disc. A Cauchy
circle then transfers that bound to the derivative on any smaller disc.
-/

namespace NLS.ComplexAnalysis
open Set Metric

/-- An entire function inherits its boundary bound throughout the closed disc. -/
theorem norm_le_of_sphere_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) {R : ℝ} (hR : 0 < R) (B : ℝ)
    (hb : ∀ w ∈ sphere c R, ‖f w‖ ≤ B) {z : ℂ} (hz : ‖z-c‖ ≤ R) : ‖f z‖ ≤ B := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := c) (r := R)) hf.diffContOnCl
  · intro w hw
    rw [frontier_ball _ hR.ne'] at hw
    exact hb w hw
  · rw [closure_ball c hR.ne']
    simpa only [mem_closedBall, dist_eq_norm] using hz

/-- A larger closed-disc bound controls the derivative on a smaller concentric disc. -/
theorem norm_deriv_le_of_closedDisc_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) {r R : ℝ} (hrR : r < R) (B : ℝ)
    (hb : ∀ w : ℂ, ‖w-c‖ ≤ R → ‖f w‖ ≤ B) {z : ℂ} (hz : ‖z-c‖ ≤ r) :
    ‖deriv f z‖ ≤ B/(R-r) := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (sub_pos.mpr hrR) hf.diffContOnCl
  intro w hw
  apply hb
  have hd : ‖w-z‖ = R-r := by simpa only [mem_sphere, dist_eq_norm] using hw
  calc
    ‖w-c‖ ≤ ‖w-z‖+‖z-c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (R-r)+r := add_le_add hd.le hz
    _ = R := sub_add_cancel _ _

end NLS.ComplexAnalysis
