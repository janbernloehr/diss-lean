import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A common positive margin for finitely many ordered pairs

A finite collection of positive separations admits one positive margin
whose double is bounded by every separation.
-/

namespace NLS.ComplexAnalysis

/-- One positive margin works for every ordered pair in a finite set. -/
theorem exists_positive_margin_for_finite_pairs {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (g : ι → ι → ℝ)
    (hg : ∀ i ∈ s, ∀ j ∈ s, i < j → 0 < g i j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ∀ j ∈ s, i < j → 2 * ε ≤ g i j := by
  classical
  let t := (s.product s).filter (fun ij : ι × ι => ij.1 < ij.2)
  by_cases ht : t.Nonempty
  · obtain ⟨ij, hij, hmin⟩ := Finset.exists_min_image t
      (fun ij : ι × ι => g ij.1 ij.2) ht
    have hij' : ij.1 ∈ s ∧ ij.2 ∈ s ∧ ij.1 < ij.2 := by
      have hh : (ij.1 ∈ s ∧ ij.2 ∈ s) ∧ ij.1 < ij.2 := by
        simpa [t, Finset.mem_filter, Finset.mem_product] using hij
      exact ⟨hh.1.1, hh.1.2, hh.2⟩
    refine ⟨g ij.1 ij.2 / 2, by linarith [hg ij.1 hij'.1 ij.2 hij'.2.1 hij'.2.2], ?_⟩
    intro i hi j hj hlt
    have hp : (i, j) ∈ t := by simp [t, hi, hj, hlt]
    have h := hmin (i, j) hp
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro i hi j hj hlt
    have hp : (i, j) ∈ t := by simp [t, hi, hj, hlt]
    exact False.elim (ht ⟨(i, j), hp⟩)

end NLS.ComplexAnalysis
