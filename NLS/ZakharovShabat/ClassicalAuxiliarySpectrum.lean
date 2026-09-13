import NLS.ZakharovShabat.ClassicalAuxiliaryExtension
import NLS.ZakharovShabat.AuxiliarySpectrum

/-!
# Original physical auxiliary eigenvalues and the actual coefficient spectrum

Both auxiliary problems use the source Neumann potential extension. Its
coefficients are defined by the actual physical Fourier integrals. The potential
phase intertwines this extension with the ordinary Dirichlet extension, giving
exact equality of the original physical and auxiliary coefficient eigenvalue sets.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.Fourier

/-- Constant multiplication commutes with the normalized physical Fourier integral. -/
theorem periodTwoCoefficient_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    periodTwoCoefficient (fun x => c * f x) n = c * periodTwoCoefficient f n := by
  unfold periodTwoCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

end NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The source Neumann extension of an arbitrary physical L² potential. -/
def neumannPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : PairSpace 2 :=
  (periodTwoL2Coefficients (fun x => (intervalExtension .neumann φ x).1)
      (memLp_intervalExtension .neumann φ hφ).fst,
    periodTwoL2Coefficients (fun x => (intervalExtension .neumann φ x).2)
      (memLp_intervalExtension .neumann φ hφ).snd)

@[simp] theorem neumannPotentialCoefficients_fst (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (neumannPotentialCoefficients φ hφ).1 n =
      periodTwoCoefficient (fun x => (intervalExtension .neumann φ x).1) n := rfl

@[simp] theorem neumannPotentialCoefficients_snd (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (neumannPotentialCoefficients φ hφ).2 n =
      periodTwoCoefficient (fun x => (intervalExtension .neumann φ x).2) n := rfl

/-- Potential conjugation changes the Neumann potential extension to the ordinary Dirichlet one. -/
theorem intervalExtension_physicalAuxiliaryPotential (φ : ℝ → ℂ × ℂ) :
    intervalExtension .dirichlet (physicalAuxiliaryPotential φ) =
      physicalAuxiliaryPotential (intervalExtension .neumann φ) := by
  funext x
  by_cases hx : x ≤ 1
  · simp only [intervalExtension_left _ _ x hx, physicalAuxiliaryPotential]
  · rw [intervalExtension_right _ _ x (lt_of_not_ge hx)]
    simp [physicalAuxiliaryPotential, intervalExtension_right _ _ x (lt_of_not_ge hx), extensionSign]

/-- Exact potential compatibility, proved from physical Fourier integrals. -/
theorem auxiliaryPotential_neumannPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    auxiliaryPotential (neumannPotentialCoefficients φ hφ) =
      dirichletPotentialCoefficients (physicalAuxiliaryPotential φ) (memLp_physicalAuxiliaryPotential φ hφ) := by
  apply Prod.ext <;> ext n
  · simp only [auxiliaryPotential_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      neumannPotentialCoefficients_fst, dirichletPotentialCoefficients_fst,
      intervalExtension_physicalAuxiliaryPotential, physicalAuxiliaryPotential, periodTwoCoefficient_const_mul]
  · simp only [auxiliaryPotential_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      neumannPotentialCoefficients_snd, dirichletPotentialCoefficients_snd,
      intervalExtension_physicalAuxiliaryPotential, physicalAuxiliaryPotential, periodTwoCoefficient_const_mul]

theorem neumannPotentialCoefficients_mem (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : neumannPotentialCoefficients φ hφ ∈ neumannSubspace := by
  apply (auxiliaryPotential_mem_dirichlet_iff _).mp
  rw [auxiliaryPotential_neumannPotentialCoefficients]
  exact dirichletPotentialCoefficients_mem _ _

/-- These coefficients synthesize the actual source Neumann potential extension. -/
theorem physicalBase_neumannPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    physicalBase (neumannPotentialCoefficients φ hφ) =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension .neumann φ := by
  filter_upwards [circlePullback_periodTwoL2Coefficients _ (memLp_intervalExtension .neumann φ hφ).fst,
    circlePullback_periodTwoL2Coefficients _ (memLp_intervalExtension .neumann φ hφ).snd] with x h₁ h₂
  exact Prod.ext h₁ h₂

/-- The actual coefficient potential agrees with the original potential on its interval. -/
theorem physicalBase_neumannPotentialCoefficients_restrict (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    physicalBase (neumannPotentialCoefficients φ hφ) =ᵐ[volume.restrict (Ioc 0 1)] φ := by
  have h := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) (physicalBase_neumannPotentialCoefficients φ hφ)
  filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  exact hx.trans (intervalExtension_left .neumann φ x hmem.2)

/-- The source auxiliary extension carries the original differential equation
into the actual coefficient operator equation. -/
theorem classical_auxiliary_equation_transfer (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f) (z : ℂ)
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    operator (by simp) (neumannPotentialCoefficients φ hφ) (classicalAuxiliaryExtension b f hf) =
      z • domainInclusion (classicalAuxiliaryExtension b f hf) := by
  let g := physicalAuxiliaryPhase.symm f
  have hg : physicalAuxiliaryPhase g = f := physicalAuxiliaryPhase.apply_symm_apply f
  have he : physicalOperator (physicalAuxiliaryPotential φ) g =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => z • g x) := by
    rw [← hg, physicalOperator_auxiliaryPhase] at h
    filter_upwards [h] with x hx
    apply (auxiliaryPhase ℂ).injective
    exact hx.trans (map_smul (auxiliaryPhase ℂ) z (g x)).symm
  unfold classicalAuxiliaryExtension
  rw [operator_auxiliaryPhase, auxiliaryPotential_neumannPotentialCoefficients,
    classical_interval_equation_transfer b _ _ (memLp_physicalAuxiliaryPotential φ hφ)
      ((hasClassicalAuxiliaryDomain_iff b f).mp hf) z he,
    domainInclusion_auxiliaryPhase, map_smul]

/-- An auxiliary coefficient equation restricts to the original physical equation. -/
theorem classical_auxiliary_equation_restrict (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (a : Domain 2) (z : ℂ)
    (h : operator (by simp) (neumannPotentialCoefficients φ hφ) a = z • domainInclusion a) :
    physicalOperator φ (classicalIntervalRestriction a) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => z • classicalIntervalRestriction a x) := by
  have he := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) ((operator_eq_smul_iff_physical _ a z).mp h)
  filter_upwards [he, physicalBase_neumannPotentialCoefficients_restrict φ hφ] with x hx hpot
  change physicalOperator φ (physicalDomain a) x = z • physicalDomain a x
  simpa only [physicalOperator, hpot] using hx

/-- The eigenvalues defined by original physical auxiliary endpoints are exactly
those of the actual auxiliary coefficient pencil at the Neumann-extended potential. -/
theorem classicalAuxiliaryEigenvalues_eq_auxiliarySpectrum (b : BoundaryCondition)
    (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    classicalAuxiliaryEigenvalues b φ = auxiliarySpectrum b (by simp)
      (neumannPotentialCoefficients φ hφ) (neumannPotentialCoefficients_mem φ hφ) := by
  rw [classicalAuxiliaryEigenvalues_eq, classicalEigenvalues_eq_boundarySpectrum b _
    (memLp_physicalAuxiliaryPotential φ hφ), auxiliarySpectrum_eq]
  congr 1
  exact (auxiliaryPotential_neumannPotentialCoefficients φ hφ).symm

end NLS.ZakharovShabat.BoundaryCondition
