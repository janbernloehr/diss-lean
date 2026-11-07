import Mathlib.Analysis.Complex.Basic

/-! A single tolerance for four complex factors near one. -/
open Complex Metric
namespace NLS.ComplexAnalysis

theorem exists_fourFactor_tolerance (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b c d : ℂ,
      ‖a-1‖ < δ → ‖b-1‖ < δ → ‖c-1‖ < δ → ‖d-1‖ < δ → ‖a*b*c*d-1‖ < ε := by
  let F : ℂ × ℂ × ℂ × ℂ → ℂ := fun t => t.1*t.2.1*t.2.2.1*t.2.2.2
  have hc : ContinuousAt F (1,1,1,1) := by fun_prop
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ,hδ,?_⟩
  intro a b c d ha hb hc hd
  have ht : dist (a,b,c,d) (1,1,1,1) < δ := by
    rw [Prod.dist_eq,Prod.dist_eq,Prod.dist_eq]
    simpa only [dist_eq_norm,max_lt_iff] using And.intro ha (And.intro hb (And.intro hc hd))
  have h := hbound ht
  simpa only [F,one_mul,dist_eq_norm] using h

end NLS.ComplexAnalysis
