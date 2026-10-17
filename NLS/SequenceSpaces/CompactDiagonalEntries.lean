import NLS.SequenceSpaces.TotalBoundedTails

/-! # Vanishing diagonal observations of compact operators

For any bounded family of input vectors, compactness makes their matching
output coordinates tend uniformly to zero at large signed indices. The
exponent is finite; the input family need not be weakly null.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compact images of a bounded family have uniformly small matching tail coordinates. -/
theorem exists_compactOperator_diagonal_tail
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hp : p ≠ ⊤) (T : E →L[ℂ] Coeff p) (hT : IsCompactOperator T)
    (v : ℤ → E) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs → ‖T (v n) n‖ < ε := by
  have hB : Bornology.IsBounded (range v) := isBounded_iff_forall_norm_le.mpr
    ⟨C,by rintro x ⟨n,rfl⟩; exact hv n⟩
  have hK := hT.isCompact_closure_image_of_bounded hB
  obtain ⟨S,hS⟩ := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_norm_tail_of_isCompact hp hK) ε hε).exists
  refine ⟨S.sup Int.natAbs+1,fun n hn => ?_⟩
  have hnS : n ∉ S := by
    intro h
    have hb := Finset.le_sup (f := Int.natAbs) h
    omega
  have hx : T (v n) ∈ closure (T '' range v) := subset_closure ⟨v n,⟨n,rfl⟩,rfl⟩
  have ht : ‖T (v n)-truncate S (T (v n))‖ < ε := by simpa using hS (T (v n)) hx
  have he : T (v n) n = (T (v n)-truncate S (T (v n))) n := by simp [truncate_apply,hnS]
  rw [he]
  exact (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' _ n).trans_lt ht

end NLS.Coeff
