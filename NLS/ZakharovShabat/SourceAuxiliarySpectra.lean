import NLS.ZakharovShabat.SourceAuxiliaryOperators

/-!
# Actual original auxiliary spectra and physical eigenvalues

The spectrum defined by bijectivity of the original restricted pencil is
closed, discrete, and finite in bounded regions. For physical L² input it
is exactly the classical auxiliary interval eigenvalue set. This identifies
the objects entering Proposition 5.2; its uniform counts and printed height
remain separate assertions.
-/

noncomputable section
open scoped ENNReal
open MeasureTheory Set
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual restricted source spectrum is closed. -/
theorem isClosed_sourceAuxiliarySpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) :
    IsClosed (sourceAuxiliarySpectrum b hp φ hφ) := by
  rw [sourceAuxiliarySpectrum_eq]
  exact isClosed_auxiliarySpectrum b hp _ hφ

/-- The actual restricted source spectrum is discrete. -/
theorem discreteTopology_sourceAuxiliarySpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) :
    DiscreteTopology (sourceAuxiliarySpectrum b hp φ hφ) := by
  rw [sourceAuxiliarySpectrum_eq]
  exact discreteTopology_auxiliarySpectrum b hp _ hφ

/-- Every bounded region contains only finitely many original auxiliary spectral values. -/
theorem finite_sourceAuxiliarySpectrum_inter (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann)
    {K : Set ℂ} (hK : Bornology.IsBounded K) : Set.Finite (sourceAuxiliarySpectrum b hp φ hφ ∩ K) := by
  rw [sourceAuxiliarySpectrum_eq]
  exact finite_auxiliarySpectrum_inter_of_isBounded b hp _ hφ hK

/-- The actual physical Neumann-reflected coefficients satisfy the original source symmetry. -/
theorem sourceNeumannPotentialCoefficients_mem (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    sourceNeumannPotentialCoefficients φ hφ ∈ sourceBoundaryBaseSubspace .neumann := by
  change CoeffPair.toMax 2 ((CoeffPair.toMax 2).symm (neumannPotentialCoefficients φ hφ)) ∈ neumannSubspace
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact neumannPotentialCoefficients_mem φ hφ

/-- The original source restriction has exactly the classical physical auxiliary eigenvalues. -/
theorem sourceAuxiliarySpectrum_eq_classical (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    sourceAuxiliarySpectrum b (by simp) (sourceNeumannPotentialCoefficients φ hφ)
      (sourceNeumannPotentialCoefficients_mem φ hφ) = classicalAuxiliaryEigenvalues b φ := by
  rw [sourceAuxiliarySpectrum_eq, classicalAuxiliaryEigenvalues_eq_auxiliarySpectrum b φ hφ]
  congr 1

/-- Completed original interval input gives the same physical auxiliary spectrum. -/
theorem sourceAuxiliarySpectrum_reflected_ofFunction (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    sourceAuxiliarySpectrum b (by simp)
      (sourceAuxiliaryReflectedPotential (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients φ hφ))
      (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients φ hφ)) =
      classicalAuxiliaryEigenvalues b φ := by
  rw [← sourceAuxiliarySpectrum_eq_classical b φ hφ]
  congr 1
  exact sourceAuxiliaryReflectedPotential_ofFunction φ hφ

end NLS.ZakharovShabat
