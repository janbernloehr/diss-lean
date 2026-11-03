import NLS.ComplexAnalysis.CompactCoordinateExtension

/-! # Uniqueness of compact scalar-coordinate continuation germs

Continuous lifts through a compact reference family of regular scalar
coordinates agree near the base parameter when their coordinate images
agree. The uniform-norm inverse retains the whole reference branch.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {K P : Type} [TopologicalSpace K] [CompactSpace K]
variable [NormedAddCommGroup P] [NormedSpace ℂ P]

omit [NormedSpace ℂ P] in
theorem eventually_eq_compact_coordinate_lifts
    (φ : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φ univ)
    (u : C(K,ℂ)) (hu : ∀ k, deriv φ (u k) ≠ 0)
    (H₁ H₂ : P → C(K,ℂ)) (a : P)
    (hc₁ : ContinuousAt H₁ a) (hc₂ : ContinuousAt H₂ a)
    (ha₁ : H₁ a = u) (ha₂ : H₂ a = u)
    (heq : ∀ᶠ b in 𝓝 a, ∀ k, φ (H₁ b k) = φ (H₂ b k)) :
    H₁ =ᶠ[𝓝 a] H₂ := by
  obtain ⟨G,_,_,hleft,_⟩ := exists_analytic_superposition_inverse isOpen_univ hφ u
    (subset_univ _) (fun k => isInvertible_fderiv_of_deriv_ne_zero φ (u k) (hu k))
  have h₁ : ∀ᶠ b in 𝓝 a, G (superposition φ (H₁ b)) = H₁ b := by
    have h := hc₁.tendsto
    rw [ha₁] at h
    exact h.eventually hleft
  have h₂ : ∀ᶠ b in 𝓝 a, G (superposition φ (H₂ b)) = H₂ b := by
    have h := hc₂.tendsto
    rw [ha₂] at h
    exact h.eventually hleft
  filter_upwards [h₁,h₂,heq] with b hb₁ hb₂ hb
  have hs : superposition φ (H₁ b) = superposition φ (H₂ b) := by
    ext k
    simp only [superposition_apply hφ.continuousOn (subset_univ _)]
    exact hb k
  exact hb₁.symm.trans ((congrArg G hs).trans hb₂)

end NLS.ComplexAnalysis
