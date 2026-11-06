import NLS.ComplexAnalysis.DiscBounds

/-! # Cauchy bounds from a full energy annulus -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem quarter_circle_mem_annulus (c z w : ℂ) {R : ℝ} (hR : 0 < R)
    (hz : z ∈ sphere c R) (hw : w ∈ sphere z (R/4)) :
    R/2 ≤ ‖w-c‖ ∧ ‖w-c‖ ≤ 2*R := by
  have hz' := mem_sphere_iff_norm.mp hz
  have hw' := mem_sphere_iff_norm.mp hw
  have hhi := norm_sub_le_norm_sub_add_norm_sub w z c
  have hlo := norm_sub_le_norm_sub_add_norm_sub z w c
  rw [norm_sub_rev z w] at hlo
  constructor <;> linarith

theorem norm_deriv_le_of_annulus_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) {R : ℝ} (hR : 0 < R) (B : ℝ)
    (hb : ∀ w : ℂ, R/2 ≤ ‖w-c‖ → ‖w-c‖ ≤ 2*R → ‖f w‖ ≤ B)
    {z : ℂ} (hz : z ∈ sphere c R) : ‖deriv f z‖ ≤ 4*B/R := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : 0 < R/4) hf.diffContOnCl (fun w hw =>
      hb w (quarter_circle_mem_annulus c z w hR hz hw).1
        (quarter_circle_mem_annulus c z w hR hz hw).2)
  apply h.trans_eq
  ring

end NLS.ComplexAnalysis
