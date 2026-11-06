import NLS.ComplexAnalysis.AnalyticZeroCount

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- A finite family of distinct simple zeros exhausts a finite simple
zero set when its cardinality equals the actual analytic zero count. -/
theorem zero_iff_mem_of_simple_zero_count (f : ℂ → ℂ) (K : Set ℂ)
    (hfinite : (K ∩ f ⁻¹' {0}).Finite) (s : Finset ℂ)
    (hs : ∀ a∈s, a∈K ∧ f a=0)
    (horder : ∀ a∈K, f a=0 → analyticOrderNatAt f a=1)
    (hcount : analyticZeroCount f K=s.card) :
    ∀ a∈K, f a=0 ↔ a∈s := by
  let S := hfinite.toFinset
  have hS (a : ℂ) : a∈S ↔ a∈K ∧ f a=0 := by simp [S]
  have hsub : s⊆S := fun a ha => (hS a).mpr (hs a ha)
  have hc : analyticZeroCount f K=S.card := by
    rw [analyticZeroCount_eq_sum S (fun a ha => ((hS a).mp ha).1)
      (fun a ha => (hS a).mpr ha)]
    rw [Finset.sum_congr rfl (fun a ha => horder a ((hS a).mp ha).1 ((hS a).mp ha).2)]
    simp
  have he : s=S := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro a ha
  rw [he,hS]
  exact ⟨fun h => ⟨ha,h⟩,fun h => h.2⟩

end NLS.ComplexAnalysis
