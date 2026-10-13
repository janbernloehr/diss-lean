import NLS.ZakharovShabat.SourceAuxiliaryRootSpaces
import NLS.ZakharovShabat.ClassicalAuxiliaryMultiplicity

/-!
# Original auxiliary multiplicities and physical Jordan chains

The original coefficient multiplicity agrees with the dimension of the full
physical auxiliary generalized eigenspace for every interval L² potential.
Both sides are independently defined using actual Jordan chains.
-/

noncomputable section
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Full original and physical auxiliary algebraic multiplicities agree. -/
theorem sourceAuxiliaryAlgebraicMultiplicity_eq_classical (b : BoundaryCondition)
    (u : IntervalPairL2) (z : ℂ) :
    sourceAuxiliaryAlgebraicMultiplicity b (by simp)
      (sourceNeumannPotentialCoefficients (intervalL2Representative u) (memLp_intervalL2Representative u))
      (sourceNeumannPotentialCoefficients_mem _ _) z = classicalAuxiliaryAlgebraicMultiplicity b u z := by
  rw [sourceAuxiliaryAlgebraicMultiplicity_eq, classicalAuxiliaryAlgebraicMultiplicity_eq_auxiliary]
  congr 1

/-- The same full-chain multiplicity correspondence through the original interval completion. -/
theorem sourceAuxiliaryAlgebraicMultiplicity_reflected_ofFunction (b : BoundaryCondition)
    (u : IntervalPairL2) (z : ℂ) :
    sourceAuxiliaryAlgebraicMultiplicity b (by simp)
      (sourceAuxiliaryReflectedPotential (by norm_num) (by simp)
        (sourceUnitIntervalL2Coefficients (intervalL2Representative u) (memLp_intervalL2Representative u)))
      (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by simp) _) z =
        classicalAuxiliaryAlgebraicMultiplicity b u z := by
  rw [← sourceAuxiliaryAlgebraicMultiplicity_eq_classical b u z]
  congr 1
  exact sourceAuxiliaryReflectedPotential_ofFunction _ _

end NLS.ZakharovShabat
