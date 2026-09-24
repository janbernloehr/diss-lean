import NLS.ComplexAnalysis.ConvexHolomorphicLoopIntegral

/-!
# Holomorphic open-path integrals in convex domains

Affine interpolation between two smooth paths with the same endpoints
stays in a convex domain. The endpoint traces are constant, so the
open-path homotopy identity equates their holomorphic integrals.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Two twice-smooth paths with the same endpoints have equal integrals
of a holomorphic one-form when both lie in a convex domain. -/
theorem curveIntegral_eq_of_convex_paths
    (f : ℂ → ℂ) (s : Set ℂ)
    (hconv : Convex ℝ s)
    (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 2 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 2 γ₂.extend (Icc 0 1))
    (hγ₁s : ∀ u : I, γ₁ u ∈ s)
    (hγ₂s : ∀ u : I, γ₂ u ∈ s) :
    (∫ᶜ z in γ₁, holomorphicOneForm f z) =
      ∫ᶜ z in γ₂, holomorphicOneForm f z := by
  let H := ContinuousMap.Homotopy.affine (γ₁ : C(I, ℂ)) (γ₂ : C(I, ℂ))
  have hHrange : range H ⊆ s := by
    rintro z ⟨⟨t,u⟩,rfl⟩
    rw [ContinuousMap.Homotopy.affine_apply]
    exact hconv.lineMap_mem (hγ₁s u) (hγ₂s u) t.property
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  have hHt : ∀ t ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H (t,u) ∈ range H := by
    intro t _ u _
    exact ⟨(t,u),rfl⟩
  have hf' : ∀ z ∈ closure (range H), DifferentiableAt ℂ f z := by
    intro z hz
    rw [hclosed.closure_eq] at hz
    exact hf z (hHrange hz)
  have heq := curveIntegral_add_sides_eq_of_holomorphic_homotopy
    f H hHt hf' (affineHomotopy_contDiffOn hγ₁ hγ₂)
  have h₁a : γ₁ (0:I) = a := by simp
  have h₂a : γ₂ (0:I) = a := by simp
  have h₁b : γ₁ (1:I) = b := by simp
  have h₂b : γ₂ (1:I) = b := by simp
  have hleft : (H.evalAt 0).cast h₁a.symm h₂a.symm = Path.refl a := by
    apply Path.ext
    funext t
    simp [H]
  have hright : (H.evalAt 1).cast h₁b.symm h₂b.symm = Path.refl b := by
    apply Path.ext
    funext t
    simp [H]
  have hleftIntegral :
      (∫ᶜ z in H.evalAt 0, holomorphicOneForm f z) = 0 := by
    calc
      _ = ∫ᶜ z in (H.evalAt 0).cast h₁a.symm h₂a.symm, holomorphicOneForm f z := by simp
      _ = 0 := by rw [hleft]; simp
  have hrightIntegral :
      (∫ᶜ z in H.evalAt 1, holomorphicOneForm f z) = 0 := by
    calc
      _ = ∫ᶜ z in (H.evalAt 1).cast h₁b.symm h₂b.symm, holomorphicOneForm f z := by simp
      _ = 0 := by rw [hright]; simp
  rw [hleftIntegral, hrightIntegral] at heq
  simpa using heq

end NLS.ComplexAnalysis
