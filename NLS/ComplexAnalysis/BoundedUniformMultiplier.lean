import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.Linarith

/-! # Uniform convergence under a bounded fixed multiplier -/

noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

/-- A fixed bounded scalar multiplier preserves uniform convergence;
no boundedness of the approximated function is required. -/
theorem tendstoUniformlyOn_bounded_const_mul {α : Type*} {l : Filter α} {S : Set ℂ}
    {f : α → ℂ → ℂ} {g c : ℂ → ℂ} (h : TendstoUniformlyOn f g l S)
    (C : ℝ) (hC : 0 < C) (hc : ∀ z ∈ S, ‖c z‖ ≤ C) :
    TendstoUniformlyOn (fun i z => c z*f i z) (fun z => c z*g z) l S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h (ε/C) (div_pos hε hC)] with i hi
  intro z hz
  have he : dist (c z*g z) (c z*f i z) = ‖c z‖*dist (g z) (f i z) := by
    simp only [dist_eq_norm,← mul_sub,norm_mul]
  rw [he]
  calc
    _ ≤ C*dist (g z) (f i z) := mul_le_mul_of_nonneg_right (hc z hz) (dist_nonneg)
    _ < C*(ε/C) := mul_lt_mul_of_pos_left (hi z hz) hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

end NLS.ComplexAnalysis
