import NLS.SequenceSpaces.OrderedPairedUnique
import NLS.ZakharovShabat.PeriodicEndpointCutoffGrowth
import NLS.ZakharovShabat.OrderedPeriodicEndpoints

/-!
# Cutoff-independent uniqueness of ordered periodic endpoints

Enlarging the central multiset permits comparison at a common cutoff.
Ordered paired multiset uniqueness fixes both central coordinates, while
ordered distant pairs are fixed by their original spectral multiplicities.
-/

noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Ordered distant endpoint pairs agree slot by slot. -/
theorem PeriodicEndpointPair.ordered_unique {hp : p ≠ ⊤} {φ : PairSpace p} {n : ℤ} {x y a b : ℂ}
    (h : PeriodicEndpointPair hp φ n x y) (h' : PeriodicEndpointPair hp φ n a b)
    (hxy : complexLexLE x y) (hab : complexLexLE a b) : x = a ∧ y = b :=
  NLS.ordered_pair_unique complexLexLE x y a b (h.multiset_eq h') hxy hab

/-- Ordered central paired enumerations agree in both coordinates at every central index. -/
theorem CentralPeriodicLabeling.ordered_unique {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ}
    {ξ η a b : ℤ → ℂ} (h : CentralPeriodicLabeling hp φ N ξ η) (h' : CentralPeriodicLabeling hp φ N a b)
    (hw : ∀ n, complexLexLE (ξ n) (η n)) (hc : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j))
    (hw' : ∀ n, complexLexLE (a n) (b n)) (hc' : ∀ i j : ℤ, i < j → complexLexLE (b i) (a j)) :
    ∀ n : ℤ, n.natAbs ≤ N → ξ n = a n ∧ η n = b n := by
  have hu := NLS.ordered_paired_multiset_enumeration_unique complexLexLE (Finset.Icc (-(N : ℤ)) N)
    ξ η a b (h.roots.trans h'.roots.symm) (fun n _ => hw n) (fun i _ j _ hij => hc i j hij)
    (fun n _ => hw' n) (fun i _ j _ hij => hc' i j hij)
  intro n hn
  apply hu n
  simp only [Finset.mem_Icc]
  omega

/-- Complete ordered endpoint sequences agree irrespective of their chosen central cutoffs. -/
theorem PeriodicEndpointLabeling.ordered_unique {hp : p ≠ ⊤} {φ : PairSpace p} {N M : ℕ}
    {ξ η a b : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η) (h' : PeriodicEndpointLabeling hp φ M a b)
    (hw : ∀ n, complexLexLE (ξ n) (η n)) (hc : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j))
    (hw' : ∀ n, complexLexLE (a n) (b n)) (hc' : ∀ i j : ℤ, i < j → complexLexLE (b i) (a j)) :
    ξ = a ∧ η = b := by
  have he (n : ℤ) : ξ n = a n ∧ η n = b n := by
    by_cases hn : n.natAbs ≤ max N M
    · exact (h.central_at_larger_cutoff (max N M) (le_max_left _ _)).ordered_unique
        (h'.central_at_larger_cutoff (max N M) (le_max_right _ _)) hw hc hw' hc' n hn
    · exact (h.distant n (by omega)).ordered_unique (h'.distant n (by omega)) (hw n) (hw' n)
  exact ⟨funext (fun n => (he n).1),funext (fun n => (he n).2)⟩

end NLS.ZakharovShabat
