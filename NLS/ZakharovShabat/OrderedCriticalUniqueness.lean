import NLS.SequenceSpaces.OrderedEnumerationUnique
import NLS.ZakharovShabat.CriticalCutoffStability
import NLS.ZakharovShabat.OrderedCriticalProducts

/-!
# Uniqueness of ordered complete critical sequences

At a common cutoff the ordered central multisets agree entry by entry,
while the distant roots are unique in their free discs. Enlargement to a
common cutoff removes every dependence on the original cutoff choices.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N M : ℕ} {ξ η : ℤ → ℂ}

/-- Ordered complete labelings with a common cutoff have the same root at each signed index. -/
theorem CriticalPointLabeling.ordered_unique_same_cutoff
    (hξ : CriticalPointLabeling hp hp1 φ hφ N ξ) (hη : CriticalPointLabeling hp hp1 φ hφ N η)
    (hsξ : Monotone (fun n => complexLexKey (ξ n)))
    (hsη : Monotone (fun n => complexLexKey (η n))) : ξ = η := by
  have hc := NLS.ordered_finset_multiset_enumeration_unique complexLexLE
    (Finset.Icc (-(N : ℤ)) N) ξ η (hξ.central.trans hη.central.symm)
    (fun _ _ _ _ hij => hsξ hij) (fun _ _ _ _ hij => hsη hij)
  funext n
  by_cases hn : n.natAbs ≤ N
  · exact hc n (by simp only [Finset.mem_Icc]; omega)
  · have hfar : N < n.natAbs := by omega
    exact ((hη.distant n hfar).2.2.2 (ξ n) (ball_subset_closedBall (hξ.distant n hfar).1)).mp
      (hξ.is_critical n)

/-- Ordered complete critical sequences are independent of every admissible central cutoff. -/
theorem CriticalPointLabeling.ordered_unique
    (hξ : CriticalPointLabeling hp hp1 φ hφ N ξ) (hη : CriticalPointLabeling hp hp1 φ hφ M η)
    (hsξ : Monotone (fun n => complexLexKey (ξ n)))
    (hsη : Monotone (fun n => complexLexKey (η n))) : ξ = η :=
  (hξ.enlarge (max N M) (le_max_left _ _)).ordered_unique_same_cutoff
    (hη.enlarge (max N M) (le_max_right _ _)) hsξ hsη

end NLS.ZakharovShabat
