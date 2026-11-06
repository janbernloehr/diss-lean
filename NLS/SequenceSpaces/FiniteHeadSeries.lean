import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS



/-- Reassemble a finite head with a partial sum that vanishes on it. -/
theorem sum_head_add_sum_range_of_zero_on_head
    {E : Type} [AddCommMonoid E] (f g : ℕ → E) (S : Finset ℕ) (N : ℕ)
    (hS : S⊆Finset.range N) (hz : ∀ j∈S, f j=0) (heq : ∀ j∉S, f j=g j) :
    (∑ j∈S,g j)+(∑ j∈Finset.range N,f j)=∑ j∈Finset.range N,g j := by
  have hs : (∑ j∈S,g j)=∑ j∈Finset.range N,if j∈S then g j else 0 := by
    rw [← Finset.sum_filter]
    have hh : (Finset.range N).filter (fun j => j∈S)=S := by
      ext j
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨hS h,h⟩⟩
    rw [hh]
  rw [hs,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j∈S
  · rw [if_pos hj,hz j hj,add_zero]
  · rw [if_neg hj,heq j hj,zero_add]

/-- A finite head and its complementary absolutely convergent tail
recover the actual full series, including an overlapping selected index. -/
theorem sum_finite_head_add_tsum_complement
    {E : Type} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (hf : Summable f) (S : Finset ℕ) :
    (∑ j∈S,f j)+(∑' j : ℕ,if j∈S then 0 else f j)=∑' j : ℕ,f j := by
  let a : ℕ → E := fun j => if j∈S then f j else 0
  let b : ℕ → E := fun j => if j∈S then 0 else f j
  have ha : Summable a := (hf.indicator (S : Set ℕ)).congr (fun j => by simp [a,Set.indicator_apply])
  have hb : Summable b := (hf.indicator ((S : Set ℕ)ᶜ)).congr (fun j => by simp [b,Set.indicator_apply])
  have hs : (∑' j : ℕ,a j)=∑ j∈S,f j := by
    rw [tsum_eq_sum (s := S) (fun j hj => by exact if_neg hj)]
    exact Finset.sum_congr rfl (fun j hj => if_pos hj)
  rw [← hs,← ha.tsum_add hb]
  apply tsum_congr
  intro j
  dsimp only [a,b]
  by_cases hj : j∈S <;> simp only [hj,if_true,if_false,zero_add,add_zero]

end NLS
