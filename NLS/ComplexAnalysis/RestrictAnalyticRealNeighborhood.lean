import Mathlib.Topology.Basic

/-! Refine a neighborhood of an ENTIRE real source locus to its true
map domain. Analytic maps and local bounds restrict through the literal
open subsets; no norm or topology is replaced. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem exists_restricted_real_neighborhood
    {E : Type*} [TopologicalSpace E]
    (B : E → Prop) (V : Set E) (hV : IsOpen V) (hBV : ∀ q,B q → q∈V)
    (U : Set E) (hU : IsOpen U) (hBU : ∀ q,B q → q∈U) :
    ∃ W : Set E,IsOpen W ∧ (∀ q,B q → q∈W) ∧ W⊆U ∧ W⊆V := by
  exact ⟨U∩V,hU.inter hV,(fun q hq => ⟨hBU q hq,hBV q hq⟩),inter_subset_left,inter_subset_right⟩

end NLS.ComplexAnalysis
