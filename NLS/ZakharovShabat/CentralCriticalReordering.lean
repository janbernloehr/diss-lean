import NLS.SequenceSpaces.OrderedFiniteEnumeration
import NLS.ComplexAnalysis.LexicographicOrder
import NLS.ZakharovShabat.CriticalPointMultiplicity

/-!
# Reordering the central critical multiset

Any enumeration of the same central multiset can replace the finite head.
The distant roots and every analytic multiplicity are preserved.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- Replacing the central enumeration by another enumeration preserves the complete critical labeling. -/
theorem CriticalPointLabeling.relabel_central (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (α : ℤ → ℂ)
    (hα : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({α n} : Multiset ℂ)) = centralCriticalRoots hp hp1 φ hφ N) :
    CriticalPointLabeling hp hp1 φ hφ N (spliceCentralRoots N α ξ) := by
  let η := spliceCentralRoots N α ξ
  have hc : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({η n} : Multiset ℂ)) = centralCriticalRoots hp hp1 φ hφ N := by
    rw [← hα]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : ¬N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [η, spliceCentralRoots, if_neg hn']
  refine ⟨hc, ?_, ?_⟩
  · intro n hn
    simpa only [spliceCentralRoots, if_pos hn] using h.distant n hn
  · intro z
    constructor
    · intro hz
      by_cases hzc : z ∈ closedBall 0 (centralCircleRadius N)
      · have hm := (mem_centralCriticalRoots hp hp1 φ hφ N z).mpr ⟨hzc,hz⟩
        rw [← hc] at hm
        obtain ⟨n,_,hn⟩ : ∃ n ∈ Finset.Icc (-(N : ℤ)) N, η n = z := by
          simpa only [Multiset.mem_sum, Multiset.mem_singleton, eq_comm] using hm
        exact ⟨n,hn⟩
      · obtain ⟨n,hn⟩ := (h.exhaustive z).mp hz
        have hfar : N < n.natAbs := by
          by_contra hsmall
          exact hzc (hn ▸ h.central_mem n (by omega))
        exact ⟨n,by simpa only [spliceCentralRoots, if_pos hfar] using hn⟩
    · rintro ⟨n,rfl⟩
      by_cases hn : N < n.natAbs
      · simpa only [spliceCentralRoots, if_pos hn] using h.is_critical n
      · have hns : n ∈ Finset.Icc (-(N : ℤ)) N := by simp only [Finset.mem_Icc]; omega
        have hm : η n ∈ centralCriticalRoots hp hp1 φ hφ N := by
          rw [← hc]
          simp only [Multiset.mem_sum, Multiset.mem_singleton]
          exact ⟨n,hns,rfl⟩
        exact ((mem_centralCriticalRoots hp hp1 φ hφ N _).mp hm).2

/-- Central roots admit a lexicographically ordered enumeration with every repetition retained. -/
theorem CriticalPointLabeling.exists_ordered_central (h : CriticalPointLabeling hp hp1 φ hφ N ξ) :
    ∃ α : ℤ → ℂ, CriticalPointLabeling hp hp1 φ hφ N (spliceCentralRoots N α ξ) ∧
      ∀ i : ℤ, i.natAbs ≤ N → ∀ j : ℤ, j.natAbs ≤ N → i ≤ j → complexLexLE (α i) (α j) := by
  have hc : (centralCriticalRoots hp hp1 φ hφ N).card = (Finset.Icc (-(N : ℤ)) N).card := by
    rw [← h.central]
    simp
  obtain ⟨α,hα,hs⟩ := NLS.exists_ordered_finset_multiset_enumeration complexLexLE
    (Finset.Icc (-(N : ℤ)) N) (centralCriticalRoots hp hp1 φ hφ N) hc
  refine ⟨α,h.relabel_central α hα,fun i hi j hj hij => ?_⟩
  apply hs i (by simp only [Finset.mem_Icc]; omega) j (by simp only [Finset.mem_Icc]; omega) hij

end NLS.ZakharovShabat
