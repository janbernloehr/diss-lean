import NLS.ZakharovShabat.CentralPeriodicOrdering

/-! # Independent lexicographic ordering of the two central parity multisets -/
noncomputable section
set_option autoImplicit false
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each central parity multiset can be sorted on its own indices, retaining all repetitions. -/
theorem exists_ordered_centralParityLabeling (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (hc : PeriodicCountingData hp φ N) :
    ∃ ξ η : ℤ → ℂ, CentralParityLabeling hp φ N ξ η ∧
      ∀ r : ℤ, r = 0 ∨ r = 1 →
        (∀ n ∈ centralParityIndices N r, complexLexLE (ξ n) (η n)) ∧
        ∀ i ∈ centralParityIndices N r, ∀ j ∈ centralParityIndices N r,
          i < j → complexLexLE (η i) (ξ j) := by
  obtain ⟨a,b,he,hew,heo⟩ := NLS.exists_ordered_paired_multiset_enumeration complexLexLE
    (centralParityIndices N 0) (centralParityRoots hp φ N 0) (hc.card_centralParityRoots hφ 0)
  obtain ⟨c,d,ho,how,hoo⟩ := NLS.exists_ordered_paired_multiset_enumeration complexLexLE
    (centralParityIndices N 1) (centralParityRoots hp φ N 1) (hc.card_centralParityRoots hφ 1)
  let ξ : ℤ → ℂ := fun n => if n % 2 = 0 then a n else c n
  let η : ℤ → ℂ := fun n => if n % 2 = 0 then b n else d n
  have even {n : ℤ} (hn : n ∈ centralParityIndices N 0) : n % 2 = 0 := by
    simpa only [Int.zero_emod] using (Finset.mem_filter.mp hn).2
  have odd {n : ℤ} (hn : n ∈ centralParityIndices N 1) : n % 2 ≠ 0 := by
    have h := (Finset.mem_filter.mp hn).2
    omega
  refine ⟨ξ,η,⟨?_,?_⟩,?_⟩
  · rw [← he]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [ξ,η,if_pos (even hn)]
  · rw [← ho]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [ξ,η,if_neg (odd hn)]
  · intro r hr
    rcases hr with rfl | rfl
    · constructor
      · intro n hn
        simpa only [ξ,η,if_pos (even hn)] using hew n hn
      · intro i hi j hj hij
        simpa only [ξ,η,if_pos (even hi),if_pos (even hj)] using heo i hi j hj hij
    · constructor
      · intro n hn
        simpa only [ξ,η,if_neg (odd hn)] using how n hn
      · intro i hi j hj hij
        simpa only [ξ,η,if_neg (odd hi),if_neg (odd hj)] using hoo i hi j hj hij

end NLS.ZakharovShabat
