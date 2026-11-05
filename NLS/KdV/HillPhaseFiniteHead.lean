import NLS.SequenceSpaces.FiniteHeadOwnTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Low physical gaps and the own index, with overlaps counted once. -/
def hillPhaseFiniteHead (N n : ℕ) : Finset ℕ := insert (n-1) (Finset.range (N-1))

theorem mem_hillPhaseFiniteHead (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (j : ℕ) :
    j∈hillPhaseFiniteHead N n ↔ j+1<N ∨ j+1=n := by
  simp only [hillPhaseFiniteHead,Finset.mem_insert,Finset.mem_range]
  omega

theorem hillPhaseFiniteHead_subset_range (N n K : ℕ) (hN : 1≤N) (hK : max N n≤K) :
    hillPhaseFiniteHead N n⊆Finset.range K := by
  intro j hj
  simp only [hillPhaseFiniteHead,Finset.mem_insert,Finset.mem_range] at hj ⊢
  have hNK : N≤K := (le_max_left _ _).trans hK
  have hnK : n≤K := (le_max_right _ _).trans hK
  rcases hj with rfl | hj
  · by_cases hn : n=0
    · subst n
      simp only [Nat.zero_sub] at *
      omega
    · omega
  · omega

end NLS.KdV
