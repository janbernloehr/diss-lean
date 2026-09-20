import NLS.ComplexAnalysis.ZeroMultiset
import Mathlib.Data.Multiset.Filter

/-!
# Restricting analytic root multisets

The root multiset on a subset is obtained by filtering the larger multiset.
Its cardinality therefore computes the restricted analytic count without
losing repeated roots.
-/

noncomputable section
open scoped Classical
namespace NLS.ComplexAnalysis

/-- A finite analytic order support stays finite on every subset. -/
theorem hasFiniteSupport_analyticOrder_subset (f : ℂ → ℂ) {S T : Set ℂ} (hST : S ⊆ T)
    (hT : (fun z => if z ∈ T then analyticOrderNatAt f z else 0).HasFiniteSupport) :
    (fun z => if z ∈ S then analyticOrderNatAt f z else 0).HasFiniteSupport := by
  apply hT.subset
  intro z hz
  by_cases hs : z ∈ S
  · simpa only [Function.mem_support, if_pos hs, if_pos (hST hs)] using hz
  · simp only [Function.mem_support, if_neg hs, ne_eq, not_true_eq_false] at hz

/-- Filtering preserves precisely the analytic multiplicities on a subset. -/
theorem analyticZeroMultiset_subset_eq_filter (f : ℂ → ℂ) {S T : Set ℂ} (hST : S ⊆ T)
    (hT : (fun z => if z ∈ T then analyticOrderNatAt f z else 0).HasFiniteSupport) :
    analyticZeroMultiset f S (hasFiniteSupport_analyticOrder_subset f hST hT) =
      (analyticZeroMultiset f T hT).filter (fun z => z ∈ S) := by
  apply Multiset.ext.mpr
  intro z
  rw [count_analyticZeroMultiset, Multiset.count_filter, count_analyticZeroMultiset]
  by_cases hz : z ∈ S
  · simp only [if_pos hz, if_pos (hST hz)]
  · simp only [if_neg hz]

/-- The restricted analytic zero count is the cardinality of the filtered larger multiset. -/
theorem analyticZeroCount_subset_eq_card_filter (f : ℂ → ℂ) {S T : Set ℂ} (hST : S ⊆ T)
    (hT : (fun z => if z ∈ T then analyticOrderNatAt f z else 0).HasFiniteSupport) :
    analyticZeroCount f S = ((analyticZeroMultiset f T hT).filter (fun z => z ∈ S)).card := by
  rw [← analyticZeroMultiset_subset_eq_filter f hST hT, card_analyticZeroMultiset]

end NLS.ComplexAnalysis
