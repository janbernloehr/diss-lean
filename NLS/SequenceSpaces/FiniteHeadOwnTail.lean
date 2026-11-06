import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Classical

namespace NLS



/-- Split an absolutely convergent sequence into a finite head, one
specified later entry, and the remaining tail. -/
theorem sum_head_add_own_add_tsum_tail
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (hf : Summable f) (N n : ℕ) (hn : N≤n) :
    (∑ k∈Finset.range N, f k)+f n+
      (∑' k : ℕ, if N≤k ∧ k≠n then f k else 0)=∑' k : ℕ, f k := by
  let a : ℕ → E := fun k => if k<N then f k else 0
  let b : ℕ → E := fun k => if k=n then f k else 0
  let c : ℕ → E := fun k => if N≤k ∧ k≠n then f k else 0
  have ha : Summable a := by
    exact (hf.indicator {k | k<N}).congr (fun k => by simp [a,Set.indicator_apply])
  have hb : Summable b := by
    exact (hf.indicator {k | k=n}).congr (fun k => by simp [b,Set.indicator_apply])
  have hc : Summable c := by
    exact (hf.indicator {k | N≤k ∧ k≠n}).congr (fun k => by simp [c,Set.indicator_apply])
  have hasum : (∑' k, a k)=∑ k∈Finset.range N, f k := by
    rw [tsum_eq_sum (s := Finset.range N) (fun k hk => by
      simp only [Finset.mem_range,not_lt] at hk
      exact if_neg (not_lt.mpr hk))]
    exact Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))
  have hbsum : (∑' k, b k)=f n := tsum_ite_eq n f
  rw [←hasum,←hbsum,←ha.tsum_add hb,←(ha.add hb).tsum_add hc]
  apply tsum_congr
  intro k
  dsimp only [a,b,c]
  by_cases hk : k<N
  · have hkn : k≠n := by omega
    simp only [if_pos hk,if_neg hkn,not_le.mpr hk,false_and,if_false,add_zero]
  · have hNk : N≤k := by omega
    by_cases hkn : k=n
    · simp [hkn,not_lt.mpr hn]
    · simp [hk,hkn,hNk]

end NLS
