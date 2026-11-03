import NLS.MKdV.ClassicalFourthFlowRestriction

/-! # Physical renormalized fourth flow on the smooth mKdV diagonal

This consumes the shared physical Hamiltonian first-variation construction.
Subtracting the mass-dependent translation generator yields exactly the
renormalized PDE. The mass is explicit; low-regularity identification is
not inferred from this smooth vector-field calculation. -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.MKdV

/-- The physical H₄ vector field minus the common translation generator. -/
def classicalRenormalizedFourthField (M : ℂ) (a b : ℝ → ℂ) :
    (ℝ → ℂ) × (ℝ → ℂ) :=
  ((classicalNLSFourthVectorField a b).1 - fun x => 6*M*deriv a x,
   (classicalNLSFourthVectorField a b).2 - fun x => 6*M*deriv b x)

/-- Equation (2) is exactly the diagonal restriction of the renormalized physical field. -/
theorem classicalRenormalizedFourthField_diagonal (M : ℂ) (u : ℝ → ℂ) :
    classicalRenormalizedFourthField M u u =
      (fun x => -deriv (deriv (deriv u)) x + 6*((u x)^2-M)*deriv u x,
       fun x => -deriv (deriv (deriv u)) x + 6*((u x)^2-M)*deriv u x) := by
  unfold classicalRenormalizedFourthField
  rw [classicalNLSFourthVectorField_formula]
  apply Prod.ext <;> funext x <;> dsimp only [Pi.sub_apply] <;> ring

/-- The renormalized field also retains the physical mKdV energy-gradient identification. -/
theorem classicalRenormalizedFourthField_gardner (M : ℂ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) :
    classicalRenormalizedFourthField M u u =
      (deriv (classicalMKdVEnergyGradient u) - fun x => 6*M*deriv u x,
       deriv (classicalMKdVEnergyGradient u) - fun x => 6*M*deriv u x) := by
  unfold classicalRenormalizedFourthField
  rw [classicalNLSFourthVectorField_diagonal u hu]
end NLS.Articles.MKdVBelowL2
