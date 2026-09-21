import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Linear increment bounds for entire functions on fixed discs

The filled divided difference is entire and hence bounded on a compact
disc. Multiplying it by the displacement gives a uniform linear bound
for the function increment, including at the center itself.
-/

open Set Complex Metric Topology
namespace NLS.ComplexAnalysis

/-- An entire function has a displacement-proportional increment bound on every fixed closed disc. -/
theorem exists_bound_entire_increment (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z-c‖ ≤ r → ‖f z-f c‖ ≤ C*‖z-c‖ := by
  have hd : Differentiable ℂ (dslope f c) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (Filter.univ_mem : (univ : Set ℂ) ∈ 𝓝 c)).mpr
      hf.differentiableOn)
  obtain ⟨C,hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hd.continuous.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun z hz => ?_⟩
  have he : (z-c)*dslope f c z = f z-f c := by simpa only [smul_eq_mul] using sub_smul_dslope f c z
  rw [← he,norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right ((hC z (by simpa only [mem_closedBall,dist_eq_norm] using hz)).trans
    (le_max_left _ _)) (norm_nonneg _)

end NLS.ComplexAnalysis
