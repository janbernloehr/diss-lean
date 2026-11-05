import NLS.ComplexAnalysis.DiscBounds
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot
/-! # Native Banach norm bounds inside a squared frequency circle -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem norm_le_of_squared_frequency_sphere_bound (F : ℂ → B)
    (hF : Differentiable ℂ F) (c : ℂ) (r M : ℝ) (hr : 0 < r)
    (hbound : ∀ z ∈ sphere c r, ‖F (z^2)‖ ≤ M)
    (E : ℂ) (hE : sqrt E ∈ closedBall c r) : ‖F E‖ ≤ M := by
  have hf : Differentiable ℂ (fun z : ℂ => F (z^2)) := hF.comp (by fun_prop)
  have h : ‖F ((sqrt E)^2)‖ ≤ M := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := c) (r := r)) hf.diffContOnCl
    · intro z hz
      rw [frontier_ball _ hr.ne'] at hz
      exact hbound z hz
    · rw [closure_ball c hr.ne']
      exact hE
  simpa only [sq_sqrt] using h
end NLS.ComplexAnalysis
