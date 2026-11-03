import NLS.MKdV.ClassicalEnergyVariation
import NLS.ZakharovShabat.ClassicalNLSFourthVariation

/-! # The physical fourth NLS flow restricts to mKdV on smooth fields

The two vector fields use gradients certified by first variations of their
actual physical Hamiltonians. This is the m=2 smooth instance of Theorem 1,
without asserting its full low-regularity or all-order extension.
-/
noncomputable section
open Complex NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

/-- Apply the NLS Poisson structure -iJ to the certified S₄ gradient. -/
def classicalNLSFourthVectorField (a b : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  (fun x => -I*(classicalNLSFourthGradient a b).2 x,
   fun x => I*(classicalNLSFourthGradient a b).1 x)

/-- The physical fourth NLS flow has exactly the two third-order PDE components. -/
theorem classicalNLSFourthVectorField_formula (a b : ℝ → ℂ) :
    classicalNLSFourthVectorField a b =
      (fun x => -deriv (deriv (deriv a)) x+6*a x*b x*deriv a x,
       fun x => -deriv (deriv (deriv b)) x+6*a x*b x*deriv b x) := by
  apply Prod.ext <;> funext x <;>
    simp only [classicalNLSFourthVectorField, classicalNLSFourthGradient] <;>
    ring_nf <;> simp [I_sq]

/-- Theorem 1 at m=2 on smooth complex fields: the two genuine physical
Hamiltonian vector fields agree after diagonal restriction. -/
theorem classicalNLSFourthVectorField_diagonal (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) :
    classicalNLSFourthVectorField u u =
      (deriv (classicalMKdVEnergyGradient u), deriv (classicalMKdVEnergyGradient u)) := by
  rw [classicalNLSFourthVectorField_formula]
  apply Prod.ext <;> funext x <;> dsimp only <;>
    rw [deriv_classicalMKdVEnergyGradient u hu x] <;> ring

end NLS.MKdV
