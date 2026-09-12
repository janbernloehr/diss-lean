import NLS.ZakharovShabat.ClassicalIntervalRootSpaces
import NLS.ZakharovShabat.FreeBoundaryMultiplicity

/-!
# Algebraic multiplicity of the original interval operator

Multiplicity is defined as the dimension of the full physical generalized
eigenspace, including Jordan chains. The root-space equivalence proves equality
with coefficient multiplicities, rather than using that equality as a definition.
-/

noncomputable section
namespace NLS.ZakharovShabat
namespace BoundaryCondition

/-- Algebraic multiplicity of the original operator counts its full physical root space. -/
def classicalAlgebraicMultiplicity (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : ℕ :=
  Module.finrank ℂ (classicalRootSpaceTop b u z)

/-- Physical and coefficient multiplicities agree, including all generalized eigenvectors. -/
theorem classicalAlgebraicMultiplicity_eq (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAlgebraicMultiplicity b u z = algebraicMultiplicity b (by simp)
      (intervalPotentialCoefficients u) (intervalPotentialCoefficients_mem u) z :=
  (classicalRootSpaceTopEquiv b u z).finrank_eq

theorem classicalAlgebraicMultiplicity_pos_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    0 < classicalAlgebraicMultiplicity b u z ↔ z ∈ classicalSpectrum b u := by
  rw [classicalAlgebraicMultiplicity_eq, classicalSpectrum_eq_boundarySpectrum]
  exact algebraicMultiplicity_pos_iff b (by simp) _ _ z

theorem classicalAlgebraicMultiplicity_eq_zero_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAlgebraicMultiplicity b u z = 0 ↔ z ∈ classicalResolventSet b u := by
  rw [classicalAlgebraicMultiplicity_eq, mem_classicalResolventSet_iff]
  exact algebraicMultiplicity_eq_zero_iff b (by simp) _ _ z

/-- The full physical root space vanishes precisely off the spectrum. -/
theorem classicalRootSpaceTop_eq_bot_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalRootSpaceTop b u z = ⊥ ↔ z ∈ classicalResolventSet b u := by
  let : FiniteDimensional ℂ (classicalRootSpaceTop b u z) := finiteDimensional_classicalRootSpaceTop b u z
  rw [← Submodule.finrank_eq_zero]
  exact classicalAlgebraicMultiplicity_eq_zero_iff b u z

/-- Every free original boundary eigenvalue is algebraically simple, including negative odd indices. -/
theorem classicalAlgebraicMultiplicity_zero (b : BoundaryCondition) (n : ℤ) :
    classicalAlgebraicMultiplicity b 0 ((Real.pi : ℂ) * n) = 1 := by
  rw [classicalAlgebraicMultiplicity_eq]
  have hz : intervalPotentialCoefficients 0 = 0 := map_zero intervalPotentialCLM
  have h : algebraicMultiplicity b (by simp) (intervalPotentialCoefficients 0)
      (intervalPotentialCoefficients_mem 0) ((Real.pi : ℂ) * n) =
      algebraicMultiplicity (p := 2) b (by simp) 0 (by simp) ((Real.pi : ℂ) * n) := by congr 1
  rw [h]
  exact algebraicMultiplicity_zero b (by simp) n

end BoundaryCondition

/-- Periodic multiplicity of the reflected potential splits into the two original physical multiplicities. -/
theorem periodicAlgebraicMultiplicity_eq_classical_sum (u : IntervalPairL2) (z : ℂ) :
    periodicAlgebraicMultiplicity (by simp) (intervalPotentialCoefficients u) z =
      BoundaryCondition.classicalAlgebraicMultiplicity .dirichlet u z +
      BoundaryCondition.classicalAlgebraicMultiplicity .neumann u z := by
  rw [BoundaryCondition.classicalAlgebraicMultiplicity_eq, BoundaryCondition.classicalAlgebraicMultiplicity_eq]
  exact periodicAlgebraicMultiplicity_eq_boundary_sum (by simp) _ _ z

end NLS.ZakharovShabat
