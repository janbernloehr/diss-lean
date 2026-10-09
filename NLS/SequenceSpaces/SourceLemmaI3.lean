import NLS.SequenceSpaces.TotalBoundedTails
import NLS.SequenceSpaces.FourierTail

/-! # I.3 with symmetric integer cutoffs and the full set quantifiers -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Projection to the symmetric finite head, including both boundary frequencies. -/
def sourceI3Projection (N : ℕ) : Coeff p →L[ℂ] Coeff p := truncateCLM (Finset.Icc (-(N : ℤ)) N)

/-- The complementary projection in I.3. -/
def sourceI3Tail (N : ℕ) : Coeff p →L[ℂ] Coeff p := ContinuousLinearMap.id ℂ _-sourceI3Projection N

@[simp] theorem sourceI3Tail_eq (N : ℕ) (a : Coeff p) :
    sourceI3Tail N a = a-truncate (Finset.Icc (-(N : ℤ)) N) a := rfl

/-- No boundary ambiguity: the complementary head omits precisely |n|>N. -/
@[simp] theorem sourceI3Tail_apply (N : ℕ) (a : Coeff p) (n : ℤ) :
    sourceI3Tail N a n = if N < n.natAbs then a n else 0 := by
  change a n-truncate (Finset.Icc (-(N : ℤ)) N) a n = _
  by_cases hn : N < n.natAbs
  · have hx : n ∉ Finset.Icc (-(N : ℤ)) N := by simp only [Finset.mem_Icc]; omega
    simp [hx,hn]
  · have hx : n ∈ Finset.Icc (-(N : ℤ)) N := by simp only [Finset.mem_Icc]; omega
    simp [hx,hn]

/-- The existing boundary-retaining Fourier tail has exactly the shifted cutoff. -/
theorem sourceI3Tail_eq_fourierTail (N : ℕ) (a : Coeff p) : sourceI3Tail N a = fourierTail (N+1) a := by
  ext n
  simp only [sourceI3Tail_apply,fourierTail_apply,Nat.lt_iff_add_one_le]

/-- Enlarging a symmetric head decreases its complementary norm. -/
theorem norm_sourceI3Tail_antitone (a : Coeff p) : Antitone (fun N => ‖sourceI3Tail N a‖) := by
  intro M N hMN
  simp only [sourceI3Tail_eq_fourierTail]
  exact norm_fourierTail_antitone (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) a
    (Nat.add_le_add_right hMN 1)

private theorem exists_sourceI3Head_superset (s : Finset ℤ) :
    ∃ N : ℕ, 1 ≤ N ∧ s ⊆ Finset.Icc (-(N : ℤ)) N := by
  refine ⟨max 1 (s.sup Int.natAbs),le_max_left _ _,?_⟩
  intro n hn
  have h := (Finset.le_sup (f := Int.natAbs) hn).trans (le_max_right 1 (s.sup Int.natAbs))
  simp only [Finset.mem_Icc]
  omega

/-- Printed I.3: pointwise boundedness and one uniform cutoff for each positive error. -/
theorem sourceLemmaI3 (hp : p ≠ ⊤) (B : Set (Coeff p)) :
    TotallyBounded B ↔
      (∀ n : ℤ, ∃ C : ℝ, ∀ a ∈ B, ‖a n‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ a ∈ B, ‖sourceI3Tail N a‖ ≤ ε) := by
  rw [totallyBounded_iff_pointwise_uniform_finite_tails hp B]
  apply and_congr_right
  intro _
  constructor
  · intro ht ε hε
    obtain ⟨s,hs⟩ := ht ε hε
    obtain ⟨N,hN,hsN⟩ := exists_sourceI3Head_superset s
    exact ⟨N,hN,fun a ha => (norm_sub_truncate_mono s _ hsN a).trans (hs a ha)⟩
  · intro ht ε hε
    obtain ⟨N,_,hN⟩ := ht ε hε
    exact ⟨Finset.Icc (-(N : ℤ)) N,hN⟩

/-- Closedness is the only extra condition needed for compactness in the ambient Banach space. -/
theorem sourceLemmaI3_compact (hp : p ≠ ⊤) (B : Set (Coeff p)) :
    IsCompact B ↔ IsClosed B ∧
      (∀ n : ℤ, ∃ C : ℝ, ∀ a ∈ B, ‖a n‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ a ∈ B, ‖sourceI3Tail N a‖ ≤ ε) := by
  constructor
  · intro hB
    exact ⟨hB.isClosed,(sourceLemmaI3 hp B).mp hB.totallyBounded⟩
  · rintro ⟨hc,hb,ht⟩
    exact ((sourceLemmaI3 hp B).mpr ⟨hb,ht⟩).isCompact_of_isClosed hc

/-- The same criterion characterizes relative compactness, without assuming the set closed. -/
theorem sourceLemmaI3_compactClosure (hp : p ≠ ⊤) (B : Set (Coeff p)) :
    IsCompact (closure B) ↔
      (∀ n : ℤ, ∃ C : ℝ, ∀ a ∈ B, ‖a n‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ a ∈ B, ‖sourceI3Tail N a‖ ≤ ε) := by
  rw [← sourceLemmaI3 hp B]
  exact ⟨fun h => h.totallyBounded.subset subset_closure,
    fun h => h.closure.isCompact_of_isClosed isClosed_closure⟩

end NLS.Coeff
