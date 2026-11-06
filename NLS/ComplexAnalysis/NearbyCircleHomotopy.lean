import NLS.ComplexAnalysis.NestedCircleHomotopy
import Mathlib.Topology.MetricSpace.Thickening

/-! # Uniform deformation of nearby circles inside a fixed compact collar

The center and radius control the distance of corresponding circle points.
Their affine homotopy stays in the same closed collar. One geometric
bound therefore preserves the integrals of every holomorphic integrand.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem dist_circleMap_le_center_radius (c₀ c₁ : ℂ) (r₀ r₁ θ : ℝ) :
    dist (circleMap c₁ r₁ θ) (circleMap c₀ r₀ θ) ≤ dist c₁ c₀ + |r₁-r₀| := by
  rw [dist_eq_norm,dist_eq_norm]
  have he : circleMap c₁ r₁ θ - circleMap c₀ r₀ θ =
      (c₁-c₀)+((r₁-r₀ : ℝ) : ℂ)*exp ((θ : ℂ)*Complex.I) := by simp only [circleMap,ofReal_sub]; ring
  rw [he]
  have h := norm_add_le (c₁-c₀) (((r₁-r₀ : ℝ) : ℂ)*exp ((θ : ℂ)*Complex.I))
  simpa only [norm_mul,norm_exp_ofReal_mul_I,mul_one,norm_real,Real.norm_eq_abs] using h

theorem circleMap_mem_collar_of_close_centers_radii
    (c₀ c₁ : ℂ) (r₀ r₁ δ : ℝ) (hr₀ : 0 ≤ r₀)
    (hclose : dist c₁ c₀ + |r₁-r₀| ≤ δ) (θ : ℝ) :
    circleMap c₁ r₁ θ ∈ cthickening δ (sphere c₀ r₀) :=
  mem_cthickening_of_dist_le _ (circleMap c₀ r₀ θ) δ (sphere c₀ r₀)
    (circleMap_mem_sphere c₀ hr₀ θ) ((dist_circleMap_le_center_radius c₀ c₁ r₀ r₁ θ).trans hclose)

theorem circleIntegral_eq_of_close_circle_collar
    (f : ℂ → ℂ) (Ω : Set ℂ) (hf : AnalyticOnNhd ℂ f Ω)
    (c₀ c₁ : ℂ) (r₀ r₁ δ : ℝ) (hr₀ : 0 ≤ r₀)
    (hcollar : cthickening δ (sphere c₀ r₀) ⊆ Ω)
    (hclose : dist c₁ c₀ + |r₁-r₀| ≤ δ) :
    (∮ z in C(c₁,r₁), f z) = ∮ z in C(c₀,r₀), f z := by
  let ε := dist c₁ c₀ + |r₁-r₀|
  have hε : 0 ≤ ε := add_nonneg dist_nonneg (abs_nonneg _)
  let H := ContinuousMap.Homotopy.affine
    (circlePath c₀ r₀ : C(I,ℂ)) (circlePath c₁ r₁ : C(I,ℂ))
  have hdist (u : I) : dist (circlePath c₁ r₁ u) (circlePath c₀ r₀ u) ≤ ε :=
    dist_circleMap_le_center_radius c₀ c₁ r₀ r₁ ((2*Real.pi)*(u : ℝ))
  have hHΩ : range H ⊆ Ω := by
    rintro z ⟨⟨s,u⟩,rfl⟩
    apply hcollar
    apply mem_cthickening_of_dist_le _ (circlePath c₀ r₀ u) δ (sphere c₀ r₀)
    · exact circleMap_mem_sphere c₀ hr₀ ((2*Real.pi)*(u : ℝ))
    · exact (affineHomotopy_dist_left_le ε hε hdist s u).trans hclose
  have hclosed : IsClosed (range H) := (isCompact_range (map_continuous H)).isClosed
  have hd (z : ℂ) (hz : z ∈ closure (range H)) : DifferentiableAt ℂ f z := by
    rw [hclosed.closure_eq] at hz
    exact (hf z (hHΩ hz)).differentiableAt
  have he := curveIntegral_eq_of_holomorphic_homotopy f H
    (affineHomotopy_loop (γ₁ := circlePath c₀ r₀) (γ₂ := circlePath c₁ r₁))
    (t := range H) (fun s _ u _ => ⟨(s,u),rfl⟩) hd
    (affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (circlePath_contDiffOn _ _))
  simpa only [curveIntegral_circlePath] using he.symm

/-- Pointwise agreement on the circle parameterization suffices for its integral. -/
theorem circleIntegral_eq_of_circleMap_eq (f g : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (h : ∀ θ : ℝ, f (circleMap c r θ) = g (circleMap c r θ)) :
    (∮ z in C(c,r), f z) = ∮ z in C(c,r), g z := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [h θ]

end NLS.ComplexAnalysis
