import Mathlib.Topology.Separation.Connected

/-!
# Continuous functions taking finitely many values

A continuous map from a connected parameter space into a separated space
cannot change between finitely many values. This will identify spectral
levels along real potential paths.
-/

namespace NLS.ComplexAnalysis

/-- A continuous function with finite range is constant on a preconnected domain. -/
theorem continuous_eq_of_finite_range {α β : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    [TopologicalSpace β] [T1Space β] (f : α → β) (hf : Continuous f)
    (hfin : (Set.range f).Finite) (x y : α) : f x = f y := by
  have hc : IsPreconnected (Set.range f) := by
    simpa only [Set.image_univ] using isPreconnected_univ.image f hf.continuousOn
  have hs := hc.isDiscrete_iff_subsingleton.mp hfin.isDiscrete
  exact hs (Set.mem_range_self x) (Set.mem_range_self y)

end NLS.ComplexAnalysis
