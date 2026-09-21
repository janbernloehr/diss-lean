import NLS.SequenceSpaces.OrderedEnumerationUnique
import NLS.ZakharovShabat.BoundaryRootCutoffGrowth
import NLS.ZakharovShabat.BoundaryRootOrder

/-!
# Uniqueness of ordered complete boundary sequences
At a common larger cutoff, both central enumerations give the same actual
multiset. Beyond that block both sequences equal the same intrinsic simple
branches, so ordered coordinates are independent of all cutoff choices.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryRootLabeling
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {b : BoundaryCondition} {hp : p ≠ ⊤}
variable {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N M : ℕ} {ξ η : ℤ → ℂ}

/-- All ordered complete boundary labelings coincide, even when their original cutoffs differ. -/
theorem ordered_unique (hξ : BoundaryRootLabeling b hp φ hφ N ξ) (hη : BoundaryRootLabeling b hp φ hφ M η)
    (hsξ : Monotone (fun n => complexLexKey (ξ n))) (hsη : Monotone (fun n => complexLexKey (η n))) : ξ = η := by
  let K := max N M
  have hc := NLS.ordered_finset_multiset_enumeration_unique complexLexLE
    (Finset.Icc (-(K : ℤ)) K) ξ η
    ((hξ.central_at_larger_cutoff K (le_max_left _ _)).trans
      (hη.central_at_larger_cutoff K (le_max_right _ _)).symm)
    (fun _ _ _ _ hij => hsξ hij) (fun _ _ _ _ hij => hsη hij)
  funext n
  by_cases hn : n.natAbs ≤ K
  · exact hc n (by simp only [Finset.mem_Icc]; omega)
  · exact (hξ.distant n (lt_of_le_of_lt (le_max_left N M) (by omega))).trans
      (hη.distant n (lt_of_le_of_lt (le_max_right N M) (by omega))).symm

end NLS.ZakharovShabat.BoundaryRootLabeling
