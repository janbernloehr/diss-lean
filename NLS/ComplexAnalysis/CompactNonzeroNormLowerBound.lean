import NLS.ComplexAnalysis.RealIntegralZero

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.ComplexAnalysis



theorem exists_pos_norm_lower_bound_of_compactSpace
    {X : Type} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (F : X → ℂ) (hF : Continuous F) (hne : ∀ x, F x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ ‖F x‖ := by
  obtain ⟨x,_,hmin⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set X).Nonempty)
    hF.norm.continuousOn
  exact ⟨‖F x‖,norm_pos_iff.mpr (hne x),fun y => hmin (mem_univ y)⟩

end NLS.ComplexAnalysis
