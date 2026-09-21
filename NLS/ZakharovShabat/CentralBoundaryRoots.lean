import NLS.ZakharovShabat.BoundaryEigenvalues
import NLS.SequenceSpaces.FiniteEnumeration

/-!
# Central Dirichlet and Neumann roots with algebraic multiplicities
Each boundary restriction has one central slot per signed free index.
The multiset uses the actual restricted operator multiplicities, rather
than the trace-defined high-index branch at central indices.
-/

noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The actual central boundary roots, with every algebraic multiplicity retained. -/
def centralRoots (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ) : Multiset ℂ :=
  ∑ z ∈ b.centralSpectrum hp φ hφ N, Multiset.replicate (b.algebraicMultiplicity hp φ hφ z) z

/-- Each central root has exactly its original restricted-operator multiplicity. -/
theorem count_centralRoots (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ) (z : ℂ) :
    (b.centralRoots hp φ hφ N).count z =
      if z ∈ b.centralSpectrum hp φ hφ N then b.algebraicMultiplicity hp φ hφ z else 0 := by
  simp [centralRoots,Multiset.count_sum',Multiset.count_replicate]

/-- The multiset cardinality is the central algebraic count. -/
theorem card_centralRoots (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ) :
    (b.centralRoots hp φ hφ N).card = ∑ z ∈ b.centralSpectrum hp φ hφ N, b.algebraicMultiplicity hp φ hφ z := by
  simp [centralRoots]

/-- Central multiset membership is exactly membership in the actual central boundary spectrum. -/
theorem mem_centralRoots (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ) (z : ℂ) :
    z ∈ b.centralRoots hp φ hφ N ↔ z ∈ b.centralSpectrum hp φ hφ N := by
  rw [← Multiset.count_pos,count_centralRoots]
  by_cases hz : z ∈ b.centralSpectrum hp φ hφ N
  · simp only [hz,if_true,iff_true]
    exact (b.algebraicMultiplicity_pos_iff hp φ hφ z).mpr ((b.mem_centralSpectrum hp φ hφ N z).mp hz).1
  · simp [hz]

/-- The actual boundary count supplies exactly one slot per signed central index. -/
theorem card_centralRoots_of_counting (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ)
    (h : BoundaryCountingData hp φ hφ N) : (b.centralRoots hp φ hφ N).card = (Finset.Icc (-(N : ℤ)) N).card := by
  rw [card_centralRoots,h.central_multiplicity b,Int.card_Icc]
  omega

/-- Enumerate all central boundary roots without losing repetitions. -/
theorem exists_centralRootLabeling (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ)
    (h : BoundaryCountingData hp φ hφ N) :
    ∃ ξ : ℤ → ℂ, (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n} : Multiset ℂ)) = b.centralRoots hp φ hφ N :=
  NLS.exists_finset_multiset_enumeration _ _ (b.card_centralRoots_of_counting hp φ hφ N h)

end NLS.ZakharovShabat.BoundaryCondition
