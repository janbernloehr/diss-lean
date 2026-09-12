import NLS.ZakharovShabat.ClassicalIntervalTransfer
import NLS.ZakharovShabat.ClassicalIntervalRestriction
import NLS.ZakharovShabat.FreeBoundaryMultiplicity

/-!
# Original interval eigenvalues and the coefficient boundary spectra

Eigenvalues are defined directly by the differential equation on `[0,1]`,
classical `H¹` regularity, and the original endpoint conditions. Restriction
and signed extension identify these sets with the coefficient boundary spectra
for the Dirichlet-reflected potential. Consequently they are closed, discrete,
and finite in bounded regions.

This identifies eigenvalue sets; it does not construct an original interval
`L²` operator or assert an independent physical resolvent equivalence.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The coefficient potential restricts to the original potential almost everywhere. -/
theorem physicalBase_dirichletPotentialCoefficients_restrict (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    physicalBase (dirichletPotentialCoefficients φ hφ) =ᵐ[volume.restrict (Ioc 0 1)] φ := by
  have h := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num))
    (physicalBase_dirichletPotentialCoefficients φ hφ)
  filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  exact hx.trans (intervalExtension_left .dirichlet φ x hmem.2)

/-- A coefficient eigen-equation restricts to the original physical equation. -/
theorem classical_interval_equation_restrict (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (a : Domain 2) (z : ℂ)
    (h : operator (by simp) (dirichletPotentialCoefficients φ hφ) a = z • domainInclusion a) :
    physicalOperator φ (classicalIntervalRestriction a) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => z • classicalIntervalRestriction a x) := by
  have he := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num))
    ((operator_eq_smul_iff_physical _ a z).mp h)
  filter_upwards [he, physicalBase_dirichletPotentialCoefficients_restrict φ hφ] with x hx hpot
  change physicalOperator φ (physicalDomain a) x = z • physicalDomain a x
  simpa only [physicalOperator, hpot] using hx

/-- A nonzero boundary vector cannot vanish on the whole original interval. -/
theorem classicalIntervalRestriction_ne_zero (b : BoundaryCondition) (a : Domain 2)
    (ha : a ∈ domain b) (hne : a ≠ 0) :
    ¬ EqOn (classicalIntervalRestriction a) 0 (Icc 0 1) := by
  intro h
  apply hne
  apply classicalIntervalRestriction_injective_on_domain b a 0 ha (domain b).zero_mem
  intro x hx
  simpa [classicalIntervalRestriction] using h hx

/-- Original eigenvalues, defined without Fourier coefficients or a coefficient spectrum. -/
def classicalEigenvalues (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ) : Set ℂ :=
  {z | ∃ f : ℝ → ℂ × ℂ, HasClassicalIntervalDomain b f ∧
    ¬ EqOn f 0 (Icc 0 1) ∧
    physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)}

/-- Changing the potential on a null set does not change any original interval eigenvalue. -/
theorem classicalEigenvalues_congr_ae (b : BoundaryCondition) {φ ψ : ℝ → ℂ × ℂ}
    (h : φ =ᵐ[volume.restrict (Ioc 0 1)] ψ) : classicalEigenvalues b φ = classicalEigenvalues b ψ := by
  have transfer (φ ψ : ℝ → ℂ × ℂ) (h : φ =ᵐ[volume.restrict (Ioc 0 1)] ψ) :
      classicalEigenvalues b φ ⊆ classicalEigenvalues b ψ := by
    rintro z ⟨f, hf, hne, he⟩
    refine ⟨f, hf, hne, ?_⟩
    filter_upwards [he, h] with x hx hpot
    simpa only [physicalOperator, hpot] using hx
  exact Subset.antisymm (transfer φ ψ h) (transfer ψ φ h.symm)

/-- Every boundary spectral point has an original classical interval eigenfunction. -/
theorem mem_classicalEigenvalues_of_mem_boundarySpectrum (b : BoundaryCondition)
    (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (z : ℂ)
    (hz : z ∈ spectrum b (by simp) (dirichletPotentialCoefficients φ hφ)
      (dirichletPotentialCoefficients_mem φ hφ)) : z ∈ classicalEigenvalues b φ := by
  obtain ⟨a, ha, hne, he⟩ := (mem_spectrum_iff_exists_eigenvector b (by simp) _ _ z).mp hz
  exact ⟨classicalIntervalRestriction a, classicalIntervalRestriction_mem b a ha,
    classicalIntervalRestriction_ne_zero b a ha hne, classical_interval_equation_restrict φ hφ a z he⟩

/-- The original eigenvalue set equals the coefficient spectrum with the same boundary condition. -/
theorem classicalEigenvalues_eq_boundarySpectrum (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    classicalEigenvalues b φ = spectrum b (by simp) (dirichletPotentialCoefficients φ hφ)
      (dirichletPotentialCoefficients_mem φ hφ) := by
  ext z
  constructor
  · rintro ⟨f, hf, hne, he⟩
    exact classical_interval_eigenvalue_mem_boundarySpectrum b φ f hφ hf z hne he
  · exact mem_classicalEigenvalues_of_mem_boundarySpectrum b φ hφ z

/-- Original interval eigenvalues form a closed set. -/
theorem isClosed_classicalEigenvalues (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : IsClosed (classicalEigenvalues b φ) := by
  rw [classicalEigenvalues_eq_boundarySpectrum b φ hφ]
  exact isClosed_spectrum b (by simp) _ _

/-- Only finitely many original interval eigenvalues lie in a bounded region. -/
theorem finite_classicalEigenvalues_inter_of_isBounded (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Set.Finite (classicalEigenvalues b φ ∩ K) := by
  rw [classicalEigenvalues_eq_boundarySpectrum b φ hφ]
  exact finite_spectrum_inter_of_isBounded b (by simp) _ _ hK

/-- The original interval eigenvalue set has the discrete subspace topology. -/
theorem discreteTopology_classicalEigenvalues (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : DiscreteTopology (classicalEigenvalues b φ) := by
  rw [classicalEigenvalues_eq_boundarySpectrum b φ hφ]
  exact discreteTopology_spectrum b (by simp) _ _

/-- The periodic coefficient spectrum is the union of the two original interval eigenvalue sets. -/
theorem periodicSpectrum_eq_classicalEigenvalues_union (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    periodicSpectrum (by simp) (dirichletPotentialCoefficients φ hφ) =
      classicalEigenvalues .dirichlet φ ∪ classicalEigenvalues .neumann φ := by
  rw [classicalEigenvalues_eq_boundarySpectrum .dirichlet φ hφ,
    classicalEigenvalues_eq_boundarySpectrum .neumann φ hφ]
  exact periodicSpectrum_eq_boundary_union (by simp) _ _

/-- The zero original potential has exactly the full integer `π` lattice, for either boundary condition. -/
theorem classicalEigenvalues_zero (b : BoundaryCondition) : classicalEigenvalues b 0 = freeLattice := by
  have hφ : MemLp (0 : ℝ → ℂ × ℂ) 2 (volume.restrict (Ioc 0 1)) := by simp
  have hzero : dirichletPotentialCoefficients 0 hφ = 0 := by
    apply Prod.ext <;> apply Subtype.ext <;> funext n <;>
      simp [dirichletPotentialCoefficients, periodTwoCoefficient]
  rw [classicalEigenvalues_eq_boundarySpectrum b 0 hφ]
  convert spectrum_zero (p := 2) b (by simp) using 1
  congr 1

end NLS.ZakharovShabat.BoundaryCondition
