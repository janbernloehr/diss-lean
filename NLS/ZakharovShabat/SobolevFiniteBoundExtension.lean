import NLS.ZakharovShabat.SobolevSourceSmoothDensity

/-! # Extending finite-source bounds to an original Sobolev ball

Continuity and finite Fourier density transfer a scalar bound on a slightly larger ball to all original Sobolev sources.
-/

noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- A continuous bound on finite Fourier sources in a slightly larger
ball extends to every original Sobolev source in the stated ball. -/
theorem le_of_finite_sobolev_ball_bound (s : ℕ) (F : SobolevSource s → ℝ)
    (hF : Continuous F) (R C : ℝ)
    (hb : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ), ‖sobolevSourceOfFinsupp s a‖ ≤ R+1 →
      F (sobolevSourceOfFinsupp s a) ≤ C)
    (ab : SobolevSource s) (hab : ‖ab‖ ≤ R) : F ab ≤ C := by
  let S : Set (SobolevSource s) := {b | R+1 ≤ ‖b‖} ∪ {b | F b ≤ C}
  have hS : IsClosed S := (isClosed_le continuous_const continuous_norm).union (isClosed_le hF continuous_const)
  have hsub : Set.range (sobolevSourceOfFinsupp s) ⊆ S := by
    rintro _ ⟨a,rfl⟩
    by_cases h : R+1 ≤ ‖sobolevSourceOfFinsupp s a‖
    · exact Or.inl h
    · exact Or.inr (hb a (le_of_not_ge h))
  have hmem : ab ∈ S := (closure_minimal hsub hS) (denseRange_sobolevSourceOfFinsupp s ab)
  rcases hmem with h | h
  · change R+1 ≤ ‖ab‖ at h
    linarith
  · exact h

end NLS.ZakharovShabat
