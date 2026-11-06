import NLS.ComplexAnalysis.ZeroMultisetRestriction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



theorem analyticOrder_indicator_eq_of_subset_equal_count
    (f : ℂ → ℂ) {S T : Set ℂ} (hST : S ⊆ T)
    (hT : (fun z => if z ∈ T then analyticOrderNatAt f z else 0).HasFiniteSupport)
    (hc : analyticZeroCount f S=analyticZeroCount f T) (z : ℂ) :
    (if z ∈ S then analyticOrderNatAt f z else 0) =
      (if z ∈ T then analyticOrderNatAt f z else 0) := by
  classical
  have he : analyticZeroMultiset f S (hasFiniteSupport_analyticOrder_subset f hST hT) =
      analyticZeroMultiset f T hT := by
    rw [analyticZeroMultiset_subset_eq_filter f hST hT]
    apply Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _)
    rw [← analyticZeroCount_subset_eq_card_filter f hST hT,card_analyticZeroMultiset]
    exact hc.symm.le
  have hh := congrArg (fun s : Multiset ℂ => s.count z) he
  simpa only [count_analyticZeroMultiset] using hh

end NLS.ComplexAnalysis
