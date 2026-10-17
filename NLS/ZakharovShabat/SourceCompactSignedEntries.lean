import NLS.SequenceSpaces.CompactDiagonalEntries
import NLS.SequenceSpaces.SourceCotangent

/-! # Vanishing signed entries of compact source operators

All four entries on the two raw signed unit directions vanish uniformly
in the tail. No summable row majorant is inferred from compactness.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_compactOperator_pair_diagonal_tail
    (hp : p ≠ ⊤) (T : CoeffPair p →L[ℂ] (Coeff p × Coeff p)) (hT : IsCompactOperator T)
    (v : ℤ → CoeffPair p) (hv : ∀ n, ‖v n‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs → ‖(T (v n)).1 n‖ < ε ∧ ‖(T (v n)).2 n‖ < ε := by
  let P := ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)
  let Q := ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)
  obtain ⟨K₁,h₁⟩ := Coeff.exists_compactOperator_diagonal_tail hp (P.comp T) (hT.clm_comp P) v 1 hv ε hε
  obtain ⟨K₂,h₂⟩ := Coeff.exists_compactOperator_diagonal_tail hp (Q.comp T) (hT.clm_comp Q) v 1 hv ε hε
  exact ⟨max K₁ K₂,fun n hn => ⟨h₁ n (by omega),h₂ n (by omega)⟩⟩

/-- All four signed unit-direction entries of a compact operator vanish in the tail. -/
theorem exists_compactOperator_signed_block_entries_small
    (hp : p ≠ ⊤) (T : CoeffPair p →L[ℂ] (Coeff p × Coeff p)) (hT : IsCompactOperator T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs →
      ‖(T (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))).1 n‖ < ε ∧
      ‖(T (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))).2 n‖ < ε ∧
      ‖(T (CoeffPair.inrCLM (lp.single p n (1:ℂ)))).1 n‖ < ε ∧
      ‖(T (CoeffPair.inrCLM (lp.single p n (1:ℂ)))).2 n‖ < ε := by
  have hl (n : ℤ) : ‖CoeffPair.inlCLM (lp.single p (-n) (1:ℂ))‖ ≤ 1 := by
    rw [CoeffPair.norm_inlCLM,lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))]
    norm_num
  have hr (n : ℤ) : ‖CoeffPair.inrCLM (lp.single p n (1:ℂ))‖ ≤ 1 := by
    rw [CoeffPair.norm_inrCLM,lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))]
    norm_num
  obtain ⟨K₁,h₁⟩ := exists_compactOperator_pair_diagonal_tail hp T hT
    (fun n => CoeffPair.inlCLM (lp.single p (-n) (1:ℂ))) hl ε hε
  obtain ⟨K₂,h₂⟩ := exists_compactOperator_pair_diagonal_tail hp T hT
    (fun n => CoeffPair.inrCLM (lp.single p n (1:ℂ))) hr ε hε
  exact ⟨max K₁ K₂,fun n hn => ⟨(h₁ n (by omega)).1,(h₁ n (by omega)).2,h₂ n (by omega)⟩⟩

end NLS.ZakharovShabat
