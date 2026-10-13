import NLS.ZakharovShabat.SourceLemma4_1
import NLS.ZakharovShabat.ClassicalAuxiliarySpectrum

/-!
# Lemma 5.1 in the original physical and coefficient spaces

The auxiliary endpoint conditions (1.10) give actual periodic H¹ extensions
with the phase-twisted reflection (-i f₊, i f₋), with opposite signs for the
two boundary problems. Both solve the equation at the Neumann-reflected
potential. The physical transfer needs no additional integrability assumption
on the potential. For L² potentials, the original-norm weighted coefficients
solve the actual source operator equation and preserve nonzero eigenfunctions.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The auxiliary reflection preserves the actual differential equation. -/
theorem physical_auxiliary_interval_equation_transfer (b : BoundaryCondition)
    (φ f : ℝ → ℂ × ℂ) (hf : HasClassicalAuxiliaryDomain b f) (z : ℂ)
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    physicalOperator (intervalExtension .neumann φ) (auxiliaryIntervalExtension b f)
      =ᵐ[volume.restrict (Ioc 0 2)] (fun x => z • auxiliaryIntervalExtension b f x) := by
  let g := physicalAuxiliaryPhase.symm f
  have hg : physicalAuxiliaryPhase g = f := physicalAuxiliaryPhase.apply_symm_apply f
  have he : physicalOperator (physicalAuxiliaryPotential φ) g
      =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • g x) := by
    rw [← hg, physicalOperator_auxiliaryPhase] at h
    filter_upwards [h] with x hx
    apply (auxiliaryPhase ℂ).injective
    exact hx.trans (map_smul (auxiliaryPhase ℂ) z (g x)).symm
  have ht := physical_interval_equation_transfer b (physicalAuxiliaryPotential φ) g
    ((hasClassicalAuxiliaryDomain_iff b f).mp hf) z he
  change physicalOperator (intervalExtension .neumann φ)
    (physicalAuxiliaryPhase (intervalExtension b g)) =ᵐ[_] _
  rw [physicalOperator_auxiliaryPhase, ← intervalExtension_physicalAuxiliaryPotential]
  filter_upwards [ht] with x hx
  change auxiliaryPhase ℂ (physicalOperator (intervalExtension .dirichlet
    (physicalAuxiliaryPotential φ)) (intervalExtension b g) x) = _
  rw [hx, map_smul]
  rfl

/-- Original-norm Fourier coefficients of the actual Neumann-reflected potential. -/
def sourceNeumannPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : CoeffPair 2 :=
  (CoeffPair.toMax 2).symm (neumannPotentialCoefficients φ hφ)

/-- Weighted original-norm coefficients of the physical auxiliary extension. -/
def sourceClassicalAuxiliaryExtension (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) : WeightedCoeffPair (Weight.sobolev 1) 2 :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalAuxiliaryExtension b f hf)

/-- Original coefficients of the auxiliary extension solve the actual source equation. -/
theorem source_classical_auxiliary_equation_transfer (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f) (z : ℂ)
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    sourceOperator (by simp) (sourceNeumannPotentialCoefficients φ hφ)
        (sourceClassicalAuxiliaryExtension b f hf) =
      z • sourceDomainInclusion (sourceClassicalAuxiliaryExtension b f hf) := by
  change (CoeffPair.toMax 2).symm
    (operator (by simp) ((CoeffPair.toMax 2) ((CoeffPair.toMax 2).symm (neumannPotentialCoefficients φ hφ)))
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalAuxiliaryExtension b f hf)))) =
    z • (CoeffPair.toMax 2).symm (domainInclusion
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalAuxiliaryExtension b f hf))))
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [classical_auxiliary_equation_transfer b φ f hφ hf z h, map_smul]

/-- Actual periodic representatives of the original auxiliary extension. -/
def sourceClassicalAuxiliaryCircleExtension (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) : C(AddCircle (2 : ℝ), ℂ) × C(AddCircle (2 : ℝ), ℂ) :=
  (sobolevSynthesis (by simp) (sourceClassicalAuxiliaryExtension b f hf).fst,
    sobolevSynthesis (by simp) (sourceClassicalAuxiliaryExtension b f hf).snd)

theorem sourceClassicalAuxiliaryCircleExtension_regular (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) :
    HasPeriodicH1Regularity (sourceClassicalAuxiliaryCircleExtension b f hf).1 ∧
      HasPeriodicH1Regularity (sourceClassicalAuxiliaryCircleExtension b f hf).2 :=
  ⟨hasPeriodicH1Regularity_sobolevSynthesis _, hasPeriodicH1Regularity_sobolevSynthesis _⟩

theorem sourceClassicalAuxiliaryCircleExtension_reconstruct (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) :
    EqOn (fun x : ℝ => ((sourceClassicalAuxiliaryCircleExtension b f hf).1 (x : AddCircle (2 : ℝ)),
      (sourceClassicalAuxiliaryCircleExtension b f hf).2 (x : AddCircle (2 : ℝ))))
      (auxiliaryIntervalExtension b f) (Icc 0 2) :=
  fun _ hx => classicalAuxiliaryExtension_reconstruct b f hf hx

/-- Lemma 5.1: both auxiliary endpoint problems extend to actual periodic H¹ solutions. -/
theorem sourceLemma5_1 (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) (z : ℂ)
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    ∃ F : C(AddCircle (2 : ℝ), ℂ) × C(AddCircle (2 : ℝ), ℂ),
      HasPeriodicH1Regularity F.1 ∧ HasPeriodicH1Regularity F.2 ∧
      EqOn (fun x : ℝ => (F.1 (x : AddCircle (2 : ℝ)), F.2 (x : AddCircle (2 : ℝ))))
        (auxiliaryIntervalExtension b f) (Icc 0 2) ∧
      physicalOperator (intervalExtension .neumann φ)
        (fun x : ℝ => (F.1 (x : AddCircle (2 : ℝ)), F.2 (x : AddCircle (2 : ℝ))))
        =ᵐ[volume.restrict (Ioc 0 2)]
        (fun x : ℝ => z • (F.1 (x : AddCircle (2 : ℝ)), F.2 (x : AddCircle (2 : ℝ)))) := by
  let F := sourceClassicalAuxiliaryCircleExtension b f hf
  have hr := sourceClassicalAuxiliaryCircleExtension_regular b f hf
  have he := sourceClassicalAuxiliaryCircleExtension_reconstruct b f hf
  refine ⟨F, hr.1, hr.2, he, ?_⟩
  have ho := physicalOperator_congr_on_period
    (Filter.EventuallyEq.rfl (f := intervalExtension .neumann φ)) he
  have ht := physical_auxiliary_interval_equation_transfer b φ f hf z h
  filter_upwards [ho, ht, ae_restrict_mem measurableSet_Ioc] with x hx hy hm
  exact (hx.trans hy).trans (congrArg (fun u => z • u) (he (Ioc_subset_Icc_self hm)).symm)

/-- The auxiliary extension retains the original function, including both endpoints. -/
theorem sourceClassicalAuxiliaryCircleExtension_restrict (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) {x : ℝ} (hx : x ∈ Icc 0 1) :
    ((sourceClassicalAuxiliaryCircleExtension b f hf).1 (x : AddCircle (2 : ℝ)),
      (sourceClassicalAuxiliaryCircleExtension b f hf).2 (x : AddCircle (2 : ℝ))) = f x :=
  classicalAuxiliaryExtension_restrict b f hf hx

/-- A nonzero physical auxiliary eigenfunction gives nonzero original weighted coefficients. -/
theorem sourceClassicalAuxiliaryExtension_ne_zero (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) (hne : ¬ EqOn f 0 (Icc 0 1)) :
    sourceClassicalAuxiliaryExtension b f hf ≠ 0 := by
  intro h
  have he := congrArg (WeightedCoeffPair.toMax (Weight.sobolev 1) 2) h
  have hz : classicalAuxiliaryExtension b f hf = 0 := by
    simpa only [sourceClassicalAuxiliaryExtension, ContinuousLinearEquiv.apply_symm_apply, map_zero] using he
  apply hne
  intro x hx
  have hr := classicalAuxiliaryExtension_restrict b f hf hx
  rw [hz] at hr
  change f x = (0, 0)
  simpa [classicalIntervalRestriction] using hr.symm

/-- Both auxiliary boundary problems produce actual source eigenvectors. -/
theorem source_classical_auxiliary_eigenvector_transfer (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f) (z : ℂ)
    (hne : ¬ EqOn f 0 (Icc 0 1))
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    ∃ a : WeightedCoeffPair (Weight.sobolev 1) 2, a ≠ 0 ∧
      sourceOperator (by simp) (sourceNeumannPotentialCoefficients φ hφ) a = z • sourceDomainInclusion a :=
  ⟨sourceClassicalAuxiliaryExtension b f hf, sourceClassicalAuxiliaryExtension_ne_zero b f hf hne,
    source_classical_auxiliary_equation_transfer b φ f hφ hf z h⟩

/-- The potential's original coefficients are exactly the physical Fourier integrals. -/
theorem sourceNeumannPotentialCoefficients_coefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (sourceNeumannPotentialCoefficients φ hφ).fst n =
      periodTwoCoefficient (fun x => (intervalExtension .neumann φ x).1) n ∧
    (sourceNeumannPotentialCoefficients φ hφ).snd n =
      periodTwoCoefficient (fun x => (intervalExtension .neumann φ x).2) n := ⟨rfl, rfl⟩

/-- These original coefficients synthesize the actual Neumann-reflected potential. -/
theorem sourceNeumannPotentialCoefficients_reconstruct (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    physicalBase (CoeffPair.toMax 2 (sourceNeumannPotentialCoefficients φ hφ))
      =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension .neumann φ := by
  unfold sourceNeumannPotentialCoefficients
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact physicalBase_neumannPotentialCoefficients φ hφ

/-- The auxiliary weighted coefficients retain the actual physical Fourier integrals. -/
theorem sourceClassicalAuxiliaryExtension_coefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) (n : ℤ) :
    (sourceClassicalAuxiliaryExtension b f hf).fst.val n =
      periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b f x).1) n ∧
    (sourceClassicalAuxiliaryExtension b f hf).snd.val n =
      periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b f x).2) n := by
  constructor
  · change (classicalIntervalExtension b (physicalAuxiliaryPhase.symm f) ((hasClassicalAuxiliaryDomain_iff b f).mp hf)).1.val n = _
    exact classicalIntervalExtension_fst b _ _ n
  · change Complex.I * (classicalIntervalExtension b (physicalAuxiliaryPhase.symm f) ((hasClassicalAuxiliaryDomain_iff b f).mp hf)).2.val n =
      periodTwoCoefficient (fun x => Complex.I * (intervalExtension b (physicalAuxiliaryPhase.symm f) x).2) n
    rw [periodTwoCoefficient_const_mul, classicalIntervalExtension_snd]


/-- An original auxiliary eigenvalue belongs to the actual periodic source spectrum. -/
theorem source_classical_auxiliary_eigenvalue_mem_spectrum (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f) (z : ℂ)
    (hne : ¬ EqOn f 0 (Icc 0 1))
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    z ∈ (sourceResolventSet (by simp) (sourceNeumannPotentialCoefficients φ hφ))ᶜ := by
  rw [sourceResolventSet_eq]
  change z ∈ periodicSpectrum (by simp) (neumannPotentialCoefficients φ hφ)
  apply (mem_periodicSpectrum_iff_exists_eigenvector (by simp) _ z).mpr
  refine ⟨classicalAuxiliaryExtension b f hf, ?_, classical_auxiliary_equation_transfer b φ f hφ hf z h⟩
  intro hz
  apply sourceClassicalAuxiliaryExtension_ne_zero b f hf hne
  change (WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalAuxiliaryExtension b f hf) = 0
  rw [hz, map_zero]

end NLS.ZakharovShabat
