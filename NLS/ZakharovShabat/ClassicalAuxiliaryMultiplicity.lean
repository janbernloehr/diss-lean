import NLS.ZakharovShabat.ClassicalAuxiliaryRootSpaces
import NLS.ZakharovShabat.ClassicalIntervalMultiplicity
import NLS.ZakharovShabat.AuxiliaryRootSpaces

/-!
# Algebraic multiplicities of the original physical auxiliary operators

Multiplicity is the dimension of the actual full physical generalized
eigenspace. The proved root-space equivalence identifies it with ordinary
physical multiplicity and with the actual auxiliary coefficient multiplicity.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The original physical potential phase commutes with the actual reflected Fourier parameter map. -/
theorem intervalPotentialCoefficients_auxiliaryPotential (u : IntervalPairL2) :
    intervalPotentialCoefficients (intervalAuxiliaryPotential u) =
      auxiliaryPotential (BoundaryCondition.neumannPotentialCoefficients (intervalL2Representative u)
        (memLp_intervalL2Representative u)) := by
  rw [BoundaryCondition.auxiliaryPotential_neumannPotentialCoefficients]
  exact BoundaryCondition.dirichletPotentialCoefficients_congr_ae _ _ _ _
    (intervalL2Representative_auxiliaryPotential u)

namespace BoundaryCondition

/-- Phase conjugation identifies the independently defined physical spectra. -/
theorem classicalAuxiliarySpectrum_eq_conjugate (b : BoundaryCondition) (u : IntervalPairL2) :
    classicalAuxiliarySpectrum b u = classicalSpectrum b (intervalAuxiliaryPotential u) := by
  rw [classicalAuxiliarySpectrum, classicalAuxiliaryResolventSet_eq]
  rfl

/-- Actual physical algebraic multiplicity, including every finite Jordan chain. -/
def classicalAuxiliaryAlgebraicMultiplicity (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : ℕ :=
  Module.finrank ℂ (classicalAuxiliaryRootSpaceTop b u z)

/-- Equality follows from the proved equivalence of full physical root spaces. -/
theorem classicalAuxiliaryAlgebraicMultiplicity_eq (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryAlgebraicMultiplicity b u z = classicalAlgebraicMultiplicity b (intervalAuxiliaryPotential u) z :=
  (classicalAuxiliaryRootSpaceTopEquiv b u z).finrank_eq.symm

/-- Physical and coefficient auxiliary multiplicities agree at the actual Neumann potential extension. -/
theorem classicalAuxiliaryAlgebraicMultiplicity_eq_auxiliary (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryAlgebraicMultiplicity b u z = auxiliaryAlgebraicMultiplicity b (by simp)
      (neumannPotentialCoefficients (intervalL2Representative u) (memLp_intervalL2Representative u))
      (neumannPotentialCoefficients_mem _ _) z := by
  rw [classicalAuxiliaryAlgebraicMultiplicity_eq, classicalAlgebraicMultiplicity_eq, auxiliaryAlgebraicMultiplicity_eq]
  congr 1
  exact intervalPotentialCoefficients_auxiliaryPotential u

theorem classicalAuxiliaryAlgebraicMultiplicity_pos_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    0 < classicalAuxiliaryAlgebraicMultiplicity b u z ↔ z ∈ classicalAuxiliarySpectrum b u := by
  rw [classicalAuxiliaryAlgebraicMultiplicity_eq, classicalAlgebraicMultiplicity_pos_iff,
    classicalAuxiliarySpectrum_eq_conjugate]

theorem classicalAuxiliaryAlgebraicMultiplicity_eq_zero_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryAlgebraicMultiplicity b u z = 0 ↔ z ∈ classicalAuxiliaryResolventSet b u := by
  rw [classicalAuxiliaryAlgebraicMultiplicity_eq, classicalAuxiliaryResolventSet_eq, classicalAlgebraicMultiplicity_eq_zero_iff]

theorem classicalAuxiliaryRootSpaceTop_eq_bot_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryRootSpaceTop b u z = ⊥ ↔ z ∈ classicalAuxiliaryResolventSet b u := by
  let := finiteDimensional_classicalAuxiliaryRootSpaceTop b u z
  rw [← Submodule.finrank_eq_zero]
  exact classicalAuxiliaryAlgebraicMultiplicity_eq_zero_iff b u z

/-- Every signed free physical auxiliary eigenvalue has algebraic multiplicity one. -/
theorem classicalAuxiliaryAlgebraicMultiplicity_zero (b : BoundaryCondition) (n : ℤ) :
    classicalAuxiliaryAlgebraicMultiplicity b 0 ((Real.pi : ℂ) * n) = 1 := by
  rw [classicalAuxiliaryAlgebraicMultiplicity_eq, map_zero, classicalAlgebraicMultiplicity_zero]

end BoundaryCondition
end NLS.ZakharovShabat
