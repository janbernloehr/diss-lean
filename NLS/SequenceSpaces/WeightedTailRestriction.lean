import NLS.SequenceSpaces.WeightedDomination

/-! # Restriction of weighted integer tails

Increasing an integer tail cutoff preserves membership and does not increase the weighted norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restricting a weighted sequence to an integer tail does not increase its norm. -/
theorem exists_tail_restriction (w : Weight) (a : WeightedCoeff w p) (K : ℕ) :
    ∃ b : WeightedCoeff w p,
      (∀ n, b.val n = if K ≤ n.natAbs then a.val n else 0) ∧ ‖b‖ ≤ ‖a‖ := by
  obtain ⟨b,hb,hbn⟩ := exists_of_norm_le w a
    (fun n => if K ≤ n.natAbs then a.val n else 0) 1 (by norm_num)
    (by intro n; split_ifs <;> simp)
  exact ⟨b,hb,by simpa only [one_mul] using hbn⟩

/-- A tail realization remains uniformly bounded when its cutoff is enlarged. -/
theorem exists_tail_restriction_of_coordinates (w : Weight) (a : WeightedCoeff w p)
    (f : ℤ → ℂ) (K₀ K : ℕ) (hK : K₀ ≤ K)
    (ha : ∀ n, a.val n = if K₀ ≤ n.natAbs then f n else 0) :
    ∃ b : WeightedCoeff w p,
      (∀ n, b.val n = if K ≤ n.natAbs then f n else 0) ∧ ‖b‖ ≤ ‖a‖ := by
  obtain ⟨b,hb,hbn⟩ := exists_tail_restriction w a K
  refine ⟨b,?_,hbn⟩
  intro n
  rw [hb n,ha n]
  by_cases hn : K ≤ n.natAbs
  · simp only [if_pos hn,if_pos (hK.trans hn)]
  · simp only [if_neg hn]

end NLS.WeightedCoeff
