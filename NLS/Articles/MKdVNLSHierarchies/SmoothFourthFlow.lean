import NLS.MKdV.ClassicalFourthFlowRestriction

/-! # Theorem 1 at m=2 on smooth complex periodic potentials

The physical component gradients used here are certified by the variation
theorems imported with the vector fields. The full H² statement and all-order
extension are separate obligations.
-/
noncomputable section
open Complex NLS.ZakharovShabat NLS.MKdV
open scoped ContDiff
namespace NLS.Articles.MKdVNLSHierarchies

/-- The scalar vanishing and genuine physical vector-field identification
in Theorem 1, for m=2 and arbitrary smooth complex period-one potentials. -/
theorem theorem1_m2_smooth (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hpu : Function.Periodic u 1) :
    classicalNLSHamiltonian u u 4 = 0 ∧
      classicalNLSFourthVectorField u u =
        (deriv (classicalMKdVEnergyGradient u), deriv (classicalMKdVEnergyGradient u)) := by
  constructor
  · have h := classicalNLSHamiltonian_four_swap u u hu hu hpu hpu
    linear_combination h / 2
  · exact classicalNLSFourthVectorField_diagonal u hu

end NLS.Articles.MKdVNLSHierarchies
