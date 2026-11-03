import NLS.KdV.HillHminusOneHighGapPairs

/-! # Independence of actual rough unordered gap pairs

Exact multiplicities identify the pair as a multiset, including double
roots. Bounds can therefore use any retained pair on the same disc.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillHminusHighGapPair.pair_eq
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n r a b) :
    ({l,u} : Multiset ℂ) = {a,b} := by
  classical
  apply Multiset.ext.mpr
  intro z
  by_cases hz : z ∈ hillHminusGapSquareDisc n r
  · rw [← h.multiplicity z hz,← k.multiplicity z hz]
  · have hl : z ≠ l := fun he => hz (he ▸ ball_subset_closedBall h.left_mem)
    have hu : z ≠ u := fun he => hz (he ▸ ball_subset_closedBall h.right_mem)
    have ha : z ≠ a := fun he => hz (he ▸ ball_subset_closedBall k.left_mem)
    have hb : z ≠ b := fun he => hz (he ▸ ball_subset_closedBall k.right_mem)
    simp [hl,hu,ha,hb]

theorem HillHminusHighGapPair.eq_or_swap
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n r a b) :
    (l = a ∧ u = b) ∨ (l = b ∧ u = a) := by
  classical
  have hs : ({l,u} : Set ℂ) = {a,b} := by
    simpa using congrArg (fun s : Multiset ℂ => (s.toFinset : Set ℂ)) (h.pair_eq k)
  exact Set.pair_eq_pair_iff.mp hs

theorem HillHminusHighGapPair.norm_gap_eq
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n r a b) :
    ‖l-u‖ = ‖a-b‖ := by
  rcases h.eq_or_swap k with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact norm_sub_rev _ _

theorem HillHminusHighGapPair.norm_gap_le
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u) (hr : r ≤ Real.pi/4) :
    ‖l-u‖ ≤ 2*Real.pi^2*(n : ℕ) := by
  have hl := (mem_ball_iff_norm.mp h.left_mem).le
  have hu := (mem_ball_iff_norm.mp h.right_mem).le
  have ht := norm_sub_le_norm_sub_add_norm_sub l (((Real.pi : ℂ)*(n : ℕ))^2) u
  rw [norm_sub_rev (((Real.pi : ℂ)*(n : ℕ))^2) u] at ht
  have hc : 0 ≤ Real.pi*(n : ℕ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hr hc
  nlinarith [Real.pi_pos]

end NLS.KdV
