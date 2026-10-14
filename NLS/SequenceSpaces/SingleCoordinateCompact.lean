import NLS.SequenceSpaces.DominatedCompactness

/-! # Compact families of single-coordinate insertions -/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every single-coordinate insertion of a fixed finite-exponent sequence
lies in one compact set in the full sequence norm topology. -/
theorem exists_compact_single_insertions (hp : p ≠ ⊤) (b : Coeff p) :
    ∃ K : Set (Coeff p), IsCompact K ∧ 0 ∈ K ∧
      ∀ n : ℤ, lp.single p n (b n) ∈ K := by
  let K : Set (Coeff p) := {a | ∀ n : ℤ, ‖a n‖ ≤ ‖b n‖}
  have hc : IsClosed K := by
    simp only [K,ofPred_forall]
    exact isClosed_iInter (fun n => isClosed_le
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.norm) continuous_const)
  refine ⟨K,isCompact_of_isClosed_of_majorant hp b hc (fun _ ha => ha),?_,?_⟩
  · intro n
    simp
  · intro n m
    by_cases hmn : m = n
    · subst m; simp
    · rw [lp.single_apply_ne _ _ _ hmn]
      exact le_of_eq_of_le (norm_zero) (norm_nonneg (b m))

end NLS.Coeff
