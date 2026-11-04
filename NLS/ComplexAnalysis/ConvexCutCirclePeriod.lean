import NLS.ComplexAnalysis.NestedCircleHomotopy

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.ComplexAnalysis



theorem circleIntegral_eq_of_convex_cut_domain
    (f : ℂ → ℂ) (Ω K : Set ℂ) (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hK : IsClosed K)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hball₀ : closedBall c₀ r₀ ⊆ Ω) (hball₁ : closedBall c₁ r₁ ⊆ Ω)
    (hcut₀ : K ⊆ ball c₀ r₀) (hcut₁ : K ⊆ ball c₁ r₁)
    (hf : DifferentiableOn ℂ f (Ω \ K)) :
    (∮ z in C(c₀,r₀), f z) = ∮ z in C(c₁,r₁), f z := by
  let H := ContinuousMap.Homotopy.affine
    (circlePath c₀ r₀ : C(I,ℂ)) (circlePath c₁ r₁ : C(I,ℂ))
  have hmem (s u : I) : H (s,u) ∈ Ω \ K := by
    constructor
    · rw [show H = ContinuousMap.Homotopy.affine
        (circlePath c₀ r₀ : C(I,ℂ)) (circlePath c₁ r₁ : C(I,ℂ)) from rfl,
        ContinuousMap.Homotopy.affine_apply]
      change AffineMap.lineMap (circleMap c₀ r₀ ((2*Real.pi)*(u:ℝ)))
        (circleMap c₁ r₁ ((2*Real.pi)*(u:ℝ))) (s:ℝ) ∈ Ω
      exact hconv.lineMap_mem (hball₀ (circleMap_mem_closedBall c₀ hr₀ _))
        (hball₁ (circleMap_mem_closedBall c₁ hr₁ _)) s.property
    · intro hw
      exact (affineCircleHomotopy_ne_of_mem_both_balls c₀ c₁ (H (s,u)) r₀ r₁
        (hcut₀ hw) (hcut₁ hw) s u) rfl
  have hclosed : IsClosed (range H) := isCompact_range H.continuous |>.isClosed
  have hopen : IsOpen (Ω \ K) := hΩ.sdiff hK
  have heq := curveIntegral_eq_of_holomorphic_homotopy f H affineHomotopy_loop
    (t := range H) (fun s _ u _ => mem_range_self (s,u))
    (by
      rw [hclosed.closure_eq]
      rintro z ⟨⟨s,u⟩,rfl⟩
      exact hf.differentiableAt (hopen.mem_nhds (hmem s u)))
    (affineHomotopy_contDiffOn (circlePath_contDiffOn c₀ r₀) (circlePath_contDiffOn c₁ r₁))
  simpa only [curveIntegral_circlePath] using heq

end NLS.ComplexAnalysis
