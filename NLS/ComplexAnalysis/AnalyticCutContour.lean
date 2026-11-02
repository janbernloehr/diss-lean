import NLS.ComplexAnalysis.NestedCircleHomotopy

/-! # Contour deformation inside an analytic domain with a compact cut

Two nested circles enclosing the same cut have equal integrals for any
function analytic off that cut. Individual spectral root choices and
special quotient formulas are unnecessary.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem circleIntegral_eq_of_analytic_cut_nestedCircles
    (f : ℂ → ℂ) (U K : Set ℂ) (hf : AnalyticOnNhd ℂ f (U \ K))
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hK₀ : K ⊆ ball c₀ r₀) (hK₁ : K ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hU : closedBall c₁ r₁ ⊆ U) :
    (∮ z in C(c₀,r₀), f z) = ∮ z in C(c₁,r₁), f z := by
  let H := ContinuousMap.Homotopy.affine
    (circlePath c₀ r₀ : C(I, ℂ)) (circlePath c₁ r₁ : C(I, ℂ))
  have hclosed : IsClosed (range H) := (isCompact_range (map_continuous H)).isClosed
  have hdiff (z : ℂ) (hz : z ∈ closure (range H)) : DifferentiableAt ℂ f z := by
    rw [hclosed.closure_eq] at hz
    obtain ⟨⟨s,u⟩,rfl⟩ := hz
    apply (hf _ ⟨hU (affineCircleHomotopy_mem_outer_closedBall
      c₀ c₁ r₀ r₁ hr₀.le hr₁.le hnest s u),?_⟩).differentiableAt
    intro hcut
    exact (affineCircleHomotopy_ne_of_mem_both_balls
      c₀ c₁ _ r₀ r₁ (hK₀ hcut) (hK₁ hcut) s u) rfl
  have heq := curveIntegral_eq_of_holomorphic_homotopy f H
    (affineHomotopy_loop (γ₁ := circlePath c₀ r₀) (γ₂ := circlePath c₁ r₁))
    (t := range H) (fun s _ u _ => ⟨(s,u),rfl⟩) hdiff
    (affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (circlePath_contDiffOn _ _))
  simpa only [curveIntegral_circlePath] using heq

end NLS.ComplexAnalysis
