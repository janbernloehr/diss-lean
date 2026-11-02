import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-! # Translation of absolutely continuous interval functions -/

noncomputable section
open Set
namespace NLS.FunctionalAnalysis

/-- Translation of the argument preserves absolute continuity on the
correspondingly translated interval, for arbitrary metric targets. -/
theorem absolutelyContinuousOnInterval_comp_add_right
    {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} (a b c : ℝ)
    (hf : AbsolutelyContinuousOnInterval f (a+c) (b+c)) :
    AbsolutelyContinuousOnInterval (fun x => f (x+c)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  let D : ℕ × (ℕ → ℝ × ℝ) := (E.1, fun i => ((E.2 i).1+c,(E.2 i).2+c))
  have hmem {x : ℝ} (hx : x ∈ uIcc a b) : x+c ∈ uIcc (a+c) (b+c) := by
    simp only [uIcc, mem_Icc, min_add_add_right, max_add_add_right] at hx ⊢
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hunshift (s t x : ℝ) (hx : x ∈ uIoc (s+c) (t+c)) : x-c ∈ uIoc s t := by
    simp only [uIoc, mem_Ioc, min_add_add_right, max_add_add_right] at hx ⊢
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hD : D ∈ AbsolutelyContinuousOnInterval.disjWithin (a+c) (b+c) := by
    refine ⟨fun i hi => ⟨hmem (hE.1 i hi).1, hmem (hE.1 i hi).2⟩, ?_⟩
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro x hxi hxj
    exact disjoint_left.mp (hE.2 hi hj hij) (hunshift _ _ x hxi) (hunshift _ _ x hxj)
  have hlenD : (∑ i ∈ Finset.range D.1, dist (D.2 i).1 (D.2 i).2) < δ := by
    simpa only [D, dist_add_right] using hlen
  exact hδprop D hD hlenD

end NLS.FunctionalAnalysis
