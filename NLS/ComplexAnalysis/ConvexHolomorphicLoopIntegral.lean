import NLS.ComplexAnalysis.AffineLoopHomotopy

/-!
# Holomorphic integrals on convex sets

Every twice-smooth closed loop in a convex set contracts affinely to its
basepoint. A holomorphic one-form therefore has zero integral on it.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- A holomorphic complex one-form integrates to zero on any
twice-smooth closed loop contained in a convex set. -/
theorem curveIntegral_eq_zero_of_convex
    (f : ℂ → ℂ) (s : Set ℂ)
    (hconv : Convex ℝ s)
    (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (hγs : ∀ u : I, γ u ∈ s) :
    (∫ᶜ z in γ, holomorphicOneForm f z) = 0 := by
  let H := ContinuousMap.Homotopy.affine
    (Path.refl a : C(I, ℂ)) (γ : C(I, ℂ))
  have ha : a ∈ s := by simpa using hγs 0
  have hHrange : range H ⊆ s := by
    rintro z ⟨⟨t,u⟩, rfl⟩
    rw [ContinuousMap.Homotopy.affine_apply]
    change AffineMap.lineMap a (γ u) (t:ℝ) ∈ s
    exact hconv.lineMap_mem ha (hγs u) t.property
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  have hconst : ContDiffOn ℝ 2 (Path.refl a).extend (Icc 0 1) := by
    have heq : (Path.refl a).extend = fun _ : ℝ => a := by
      funext t
      simp
    rw [heq]
    fun_prop
  have hcontdiff := affineHomotopy_contDiffOn hconst hγ
  have hφt : ∀ t ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H (t,u) ∈ range H := by
    intro t _ u _
    exact ⟨(t,u),rfl⟩
  have hf' : ∀ z ∈ closure (range H), DifferentiableAt ℂ f z := by
    intro z hz
    rw [hclosed.closure_eq] at hz
    exact hf z (hHrange hz)
  have h := curveIntegral_eq_of_holomorphic_homotopy f H
    (affineHomotopy_loop (γ₁ := Path.refl a) (γ₂ := γ)) hφt hf' hcontdiff
  simpa using h.symm

end NLS.ComplexAnalysis
