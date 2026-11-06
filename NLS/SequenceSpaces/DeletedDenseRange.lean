import NLS.SequenceSpaces.DeletedCoordinate
import NLS.SequenceSpaces.Truncation

/-! # Retained coordinate directions determine dense range -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- Hitting every retained unit vector gives dense range in the actual
omitted-coordinate lp space, by literal finite Fourier truncations. -/
theorem denseRange_of_deletedSingle_mem_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (n : ℤ)
    (A : E →L[ℂ] DeletedCoeff p n)
    (h : ∀ k : ℤ, ∀ hk : k ≠ n, deletedSingleCLM n k hk 1 ∈ A.range) : DenseRange A := by
  have hs (k : ℤ) (c : ℂ) : deleteCoordinateTo n (lp.single p k c) ∈ A.range := by
    by_cases hk : k = n
    · subst k
      rw [deleteCoordinateTo_single_same]
      exact A.range.zero_mem
    · rw [deleteCoordinateTo_single_other n k hk]
      obtain ⟨x,hx⟩ := h k hk
      refine ⟨c • x,?_⟩
      rw [map_smul,hx,←map_smul]
      simp only [smul_eq_mul,mul_one]
  intro b
  have htr (s : Finset ℤ) : deleteCoordinateTo n (truncate s b.val) ∈ A.range := by
    rw [truncate,map_sum]
    exact Submodule.sum_mem _ (fun k _ => hs k (b.val k))
  have ht : Tendsto (fun s : Finset ℤ => deleteCoordinateTo n (truncate s b.val)) atTop (𝓝 b) := by
    have H := (deleteCoordinateTo (p := p) n).continuous.continuousAt.tendsto.comp (tendsto_truncate hp b.val)
    have hb : deleteCoordinateTo n b.val = b := by
      apply Subtype.ext
      exact (deleteCoordinate_eq_self_iff n b.val).mpr b.property
    simpa only [Function.comp_def,hb] using H
  exact mem_closure_of_tendsto ht (Eventually.of_forall htr)

end NLS.Coeff
