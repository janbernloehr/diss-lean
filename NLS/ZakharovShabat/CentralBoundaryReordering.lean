import NLS.SequenceSpaces.OrderedFiniteEnumeration
import NLS.ComplexAnalysis.LexicographicOrder
import NLS.ZakharovShabat.BoundaryRootMultiplicity
import NLS.ZakharovShabat.CompletePeriodicParityPairs

/-!
# Ordered central boundary roots
A finite central enumeration may be replaced without changing the actual
spectrum, original multiplicities, distant branches, or lp displacement.
Sorting the central multiset retains every repeated boundary root.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryRootLabeling
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {b : BoundaryCondition} {hp : p ≠ ⊤}
variable {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}

/-- Any new enumeration of the same central multiset preserves a complete boundary labeling. -/
theorem relabel_central (h : BoundaryRootLabeling b hp φ hφ N ξ) (α : ℤ → ℂ)
    (hα : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({α n} : Multiset ℂ)) = b.centralRoots hp φ hφ N) :
    BoundaryRootLabeling b hp φ hφ N (spliceCentralRoots N α ξ) := by
  refine ⟨h.counting,?_,?_,memℓp_spliceCentralRoots N α ξ h.displacement⟩
  · rw [← hα]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : ¬N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [spliceCentralRoots,if_neg hn']
  · intro n hn
    simpa only [spliceCentralRoots,if_pos hn] using h.distant n hn

/-- The central boundary multiset has an ordered enumeration retaining all algebraic repetitions. -/
theorem exists_ordered_central (h : BoundaryRootLabeling b hp φ hφ N ξ) :
    ∃ α : ℤ → ℂ, BoundaryRootLabeling b hp φ hφ N (spliceCentralRoots N α ξ) ∧
      ∀ i : ℤ, i.natAbs ≤ N → ∀ j : ℤ, j.natAbs ≤ N → i ≤ j → complexLexLE (α i) (α j) := by
  obtain ⟨α,hα,hs⟩ := NLS.exists_ordered_finset_multiset_enumeration complexLexLE
    (Finset.Icc (-(N : ℤ)) N) (b.centralRoots hp φ hφ N) (b.card_centralRoots_of_counting hp φ hφ N h.counting)
  refine ⟨α,h.relabel_central α hα,fun i hi j hj hij => ?_⟩
  exact hs i (by simp only [Finset.mem_Icc]; omega) j (by simp only [Finset.mem_Icc]; omega) hij

end NLS.ZakharovShabat.BoundaryRootLabeling
