import NLS.SequenceSpaces.EvenTailReplacement

/-! Physical conjugation of a replacement of high even Fourier pairs. -/
noncomputable section
namespace NLS

/-- Only the actually replaced pairs need the physical conjugation symmetry;
no condition on the unused low pair slots is imposed. -/
theorem evenTailReplacement_conj_of_pairs (N : ℕ) (a a' : ℤ → ℂ) (b b' : ℕ → ℂ × ℂ)
    (ha : ∀ k, a' k = (starRingEnd ℂ) (a (-k)))
    (hb : ∀ n : ℕ, 1 ≤ n → N ≤ n →
      b' n = ((starRingEnd ℂ) (b n).2, (starRingEnd ℂ) (b n).1)) (k : ℤ) :
    evenTailReplacement N a' b' k = (starRingEnd ℂ) (evenTailReplacement N a b (-k)) := by
  have he : (-k) % 2 = 0 ↔ k % 2 = 0 := by omega
  simp only [evenTailReplacement, Int.natAbs_neg, he]
  by_cases hk : k % 2 = 0 ∧ 1 ≤ k.natAbs/2 ∧ N ≤ k.natAbs/2
  · simp only [if_pos hk, hb _ hk.2.1 hk.2.2]
    have hk0 : k ≠ 0 := by rintro rfl; simpa using hk.2.1
    by_cases hs : 0 ≤ k
    · have hns : ¬0 ≤ -k := by omega
      simp only [if_pos hs, if_neg hns]
    · have hns : 0 ≤ -k := by omega
      simp only [if_neg hs, if_pos hns]
  · simp only [if_neg hk, ha]

end NLS
