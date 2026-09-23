import NLS.ComplexAnalysis.AffineLoopHomotopy
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local stability of holomorphic loop integrals

The compact image of a smooth loop in a holomorphic domain has a uniform
buffer inside that domain. Any sufficiently close smooth loop is joined
to it by an affine homotopy within the domain, so their integrals agree.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- A holomorphic one-form's integral is locally constant under uniform
perturbations of a twice-smooth closed loop inside its domain. -/
theorem exists_curveIntegral_eq_of_uniform_perturbation
    (f : ℂ → ℂ) (Ω : Set ℂ)
    (hΩopen : IsOpen Ω)
    (hf : ∀ z ∈ Ω, DifferentiableAt ℂ f z)
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (hγΩ : ∀ u : I, γ u ∈ Ω) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {b : ℂ} (η : Path b b),
        ContDiffOn ℝ 2 η.extend (Icc 0 1) →
        (∀ u : I, dist (η u) (γ u) ≤ δ) →
        (∫ᶜ z in η, holomorphicOneForm f z) =
          ∫ᶜ z in γ, holomorphicOneForm f z := by
  have hK : IsCompact (range γ) :=
    isCompact_range (map_continuous γ)
  have hKΩ : range γ ⊆ Ω := by
    rintro z ⟨u, rfl⟩
    exact hγΩ u
  obtain ⟨ε, hε, hthick⟩ :=
    hK.exists_thickening_subset_open hΩopen hKΩ
  refine ⟨ε/2, half_pos hε, ?_⟩
  intro b η hη hclose
  let H := ContinuousMap.Homotopy.affine (γ : C(I, ℂ)) (η : C(I, ℂ))
  have hHΩ : range H ⊆ Ω := by
    rintro z ⟨⟨s,u⟩, rfl⟩
    have hdist : dist (H (s,u)) (γ u) ≤ ε/2 :=
      affineHomotopy_dist_left_le (ε/2) (half_pos hε).le hclose s u
    apply hthick
    exact mem_thickening_iff.mpr
      ⟨γ u, ⟨u, rfl⟩, lt_of_le_of_lt hdist (half_lt_self hε)⟩
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  have hHt : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H (s,u) ∈ range H := by
    intro s _ u _
    exact ⟨(s,u),rfl⟩
  have hfd : ∀ z ∈ closure (range H), DifferentiableAt ℂ f z := by
    intro z hz
    rw [hclosed.closure_eq] at hz
    exact hf z (hHΩ hz)
  exact (curveIntegral_eq_of_holomorphic_homotopy f H
    (affineHomotopy_loop (γ₁ := γ) (γ₂ := η)) hHt hfd
    (affineHomotopy_contDiffOn hγ hη)).symm

end NLS.ComplexAnalysis
