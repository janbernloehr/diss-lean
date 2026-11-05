import NLS.KdV.HillHminusOneGapPairUniqueness

/-! # Intrinsic uniqueness of local H^-1 high pairs

Exact multiplicities identify the same unordered pair on any two
concentric high energy discs. This permits estimates made with different
local radii to be combined, including at a repeated root.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

theorem HillHminusHighGapPair.multiset_eq_of_radius_le
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n s a b)
    (hrs : r ≤ s) : ({l,u} : Multiset ℂ) = {a,b} := by
  have hsub : hillHminusGapSquareDisc n r ⊆ hillHminusGapSquareDisc n s :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hrs (by positivity))
  have hle : ({l,u} : Multiset ℂ) ≤ {a,b} := by
    apply Multiset.le_iff_count.mpr
    intro z
    by_cases hz : z ∈ hillHminusGapSquareDisc n r
    · rw [← h.multiplicity z hz,← k.multiplicity z (hsub hz)]
    · have hzl : z ≠ l := by rintro rfl; exact hz (ball_subset_closedBall h.left_mem)
      have hzu : z ≠ u := by rintro rfl; exact hz (ball_subset_closedBall h.right_mem)
      simp [hzl,hzu]
  exact Multiset.eq_of_le_of_card_le hle (by simp)

theorem HillHminusHighGapPair.multiset_eq
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n s a b) :
    ({l,u} : Multiset ℂ) = {a,b} := by
  rcases le_total r s with hrs | hsr
  · exact h.multiset_eq_of_radius_le k hrs
  · exact (k.multiset_eq_of_radius_le h hsr).symm

theorem HillHminusHighGapPair.eq_or_swap_of_radii
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n s a b) :
    (l = a ∧ u = b) ∨ (l = b ∧ u = a) := by
  have he := h.multiset_eq k
  have hl : l = a ∨ l = b := by
    have hm : l ∈ ({a,b} : Multiset ℂ) := he ▸ (by simp)
    simpa using hm
  rcases hl with rfl | rfl
  · left
    exact ⟨rfl,by simpa using he⟩
  · right
    have he' := he.trans (Multiset.pair_comm _ _)
    exact ⟨rfl,by simpa using he'⟩

/-- The actual radicand has total analytic count two on the complete
closed disc, with no boundary zeros. -/
theorem HillHminusHighGapPair.analyticZeroCount_eq_two
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u) :
    analyticZeroCount (fun z => hillHminusRadicand q z) (hillHminusGapSquareDisc n r) = 2 := by
  have hl := ball_subset_closedBall h.left_mem
  have hu := ball_subset_closedBall h.right_mem
  rw [analyticZeroCount_eq_sum {l,u} (by
    intro z hz
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption) (by
    intro z hz
    simpa using (h.zeros_iff z hz.1).mp hz.2)]
  by_cases hlu : l = u
  · subst u
    simp [h.multiplicity l hl]
  · simp [h.multiplicity l hl,h.multiplicity u hu,hlu,Ne.symm hlu]

end NLS.KdV
