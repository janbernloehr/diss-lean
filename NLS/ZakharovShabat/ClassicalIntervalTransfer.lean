import NLS.Fourier.IntervalL2Realization
import NLS.ZakharovShabat.IntervalEquationReflection
import NLS.ZakharovShabat.BoundarySpectrum

/-!
# Classical interval eigenfunction transfer (Lemma 4.1)

An arbitrary original `L²` potential has a Dirichlet-reflected physical Fourier
realization. For either endpoint domain, signed eigenfunction extension solves
the existing coefficient operator equation. Nonzero original eigenfunctions
give nonzero periodic eigenvectors in the selected weighted boundary domain.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

/-- Signed interval extension preserves square integrability without matching endpoint values. -/
theorem memLp_intervalExtension (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    MemLp (intervalExtension b φ) 2 (volume.restrict (Ioc 0 2)) :=
  memLp_prod_iff.mpr ⟨memLp_folded_of_memLp _ hφ.fst hφ.snd,
    memLp_folded_of_memLp _ hφ.snd hφ.fst⟩

/-- The Dirichlet-reflected potential, used for both boundary spectral problems. -/
def dirichletPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : PairSpace 2 :=
  (periodTwoL2Coefficients (fun x => (intervalExtension .dirichlet φ x).1)
      (memLp_intervalExtension .dirichlet φ hφ).fst,
    periodTwoL2Coefficients (fun x => (intervalExtension .dirichlet φ x).2)
      (memLp_intervalExtension .dirichlet φ hφ).snd)

@[simp] theorem dirichletPotentialCoefficients_fst (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (dirichletPotentialCoefficients φ hφ).1 n =
      periodTwoCoefficient (fun x => (intervalExtension .dirichlet φ x).1) n := rfl

@[simp] theorem dirichletPotentialCoefficients_snd (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (dirichletPotentialCoefficients φ hφ).2 n =
      periodTwoCoefficient (fun x => (intervalExtension .dirichlet φ x).2) n := rfl

/-- The potential coefficients reconstruct the actual reflected `L²` potential almost everywhere. -/
theorem physicalBase_dirichletPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    physicalBase (dirichletPotentialCoefficients φ hφ)
      =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension .dirichlet φ := by
  filter_upwards [circlePullback_periodTwoL2Coefficients _ (memLp_intervalExtension .dirichlet φ hφ).fst,
    circlePullback_periodTwoL2Coefficients _ (memLp_intervalExtension .dirichlet φ hφ).snd] with x h₁ h₂
  exact Prod.ext h₁ h₂

/-- The reflected potential lies in the actual Dirichlet coefficient subspace. -/
theorem dirichletPotentialCoefficients_mem (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    dirichletPotentialCoefficients φ hφ ∈ dirichletSubspace := by
  have h₁ : IntervalIntegrable (fun x => (φ x).1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hφ.fst.integrable (by norm_num))
  have h₂ : IntervalIntegrable (fun x => (φ x).2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hφ.snd.integrable (by norm_num))
  rw [mem_dirichletSubspace]
  intro n
  change periodTwoCoefficient (folded 1 (fun x => (φ x).1) (fun x => (φ x).2)) n =
    periodTwoCoefficient (folded 1 (fun x => (φ x).2) (fun x => (φ x).1)) (-n)
  rw [periodTwoCoefficient_folded_of_intervalIntegrable 1 h₁ h₂,
    periodTwoCoefficient_folded_of_intervalIntegrable 1 h₂ h₁]
  simp [add_comm]

/-- Lemma 4.1 in the actual coefficient operator, for either classical boundary condition. -/
theorem classical_interval_equation_transfer (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    operator (by simp) (dirichletPotentialCoefficients φ hφ) (classicalIntervalExtension b f hf) =
      z • domainInclusion (classicalIntervalExtension b f hf) := by
  apply (operator_eq_smul_iff_physical _ _ z).mpr
  have hrec : EqOn (physicalDomain (classicalIntervalExtension b f hf))
      (intervalExtension b f) (Icc 0 2) := fun x hx => classicalIntervalExtension_reconstruct b f hf hx
  have hop := physicalOperator_congr_on_period (physicalBase_dirichletPotentialCoefficients φ hφ) hrec
  have heq := physical_interval_equation_transfer b φ f hf z h
  apply (hop.trans heq).trans
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [hrec (Ioc_subset_Icc_self hx)]

/-- A nonzero original interval function remains nonzero after classical extension. -/
theorem classicalIntervalExtension_ne_zero (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (hne : ¬ EqOn f 0 (Icc 0 1)) :
    classicalIntervalExtension b f hf ≠ 0 := by
  intro he
  apply hne
  intro x hx
  have h := classicalIntervalExtension_restrict b f hf hx
  rw [he] at h
  change f x = (0, 0)
  simpa using h.symm

/-- Every original classical eigenfunction gives a nonzero periodic eigenvector in its boundary domain. -/
theorem classical_interval_eigenvector_transfer (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (hne : ¬ EqOn f 0 (Icc 0 1))
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    ∃ a : Domain 2, a ∈ domain b ∧ a ≠ 0 ∧
      operator (by simp) (dirichletPotentialCoefficients φ hφ) a = z • domainInclusion a :=
  ⟨classicalIntervalExtension b f hf, classicalIntervalExtension_mem b f hf,
    classicalIntervalExtension_ne_zero b f hf hne, classical_interval_equation_transfer b φ f hφ hf z h⟩

/-- The original classical eigenvalue belongs to the already-constructed boundary spectrum. -/
theorem classical_interval_eigenvalue_mem_boundarySpectrum (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (hne : ¬ EqOn f 0 (Icc 0 1))
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    z ∈ spectrum b (by simp) (dirichletPotentialCoefficients φ hφ) (dirichletPotentialCoefficients_mem φ hφ) :=
  (mem_spectrum_iff_exists_eigenvector b (by simp) _ _ z).mpr
    (classical_interval_eigenvector_transfer b φ f hφ hf z hne h)

/-- In particular, both original boundary eigenvalues are periodic eigenvalues of the Dirichlet potential extension. -/
theorem classical_interval_eigenvalue_mem_periodicSpectrum (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (hne : ¬ EqOn f 0 (Icc 0 1))
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    z ∈ periodicSpectrum (by simp) (dirichletPotentialCoefficients φ hφ) := by
  obtain ⟨a, _, ha, he⟩ := classical_interval_eigenvector_transfer b φ f hφ hf z hne h
  exact (mem_periodicSpectrum_iff_exists_eigenvector (by simp) _ z).mpr ⟨a, ha, he⟩

end NLS.ZakharovShabat.BoundaryCondition
