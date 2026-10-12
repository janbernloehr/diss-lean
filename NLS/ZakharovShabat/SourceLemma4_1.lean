import NLS.ZakharovShabat.SourceResolvent
import NLS.ZakharovShabat.ClassicalIntervalEigenvalues

/-! # Lemma 4.1 in the original physical and coefficient spaces

The actual periodic H¹ extension solves the reflected physical equation.
For L² potentials, its exact Fourier coefficients solve the original-norm
source operator equation. Nonzero original eigenfunctions remain nonzero,
and the two original interval eigenvalue sets exhaust the reflected spectrum.
-/
noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Original-norm Fourier coefficients of the reflected potential, for both boundary problems. -/
def sourceDirichletPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : CoeffPair 2 :=
  (CoeffPair.toMax 2).symm (dirichletPotentialCoefficients φ hφ)

/-- Original-norm weighted coefficients of the actual signed Sobolev extension. -/
def sourceClassicalIntervalExtension (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) : WeightedCoeffPair (Weight.sobolev 1) 2 :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalIntervalExtension b f hf)

/-- The extended function solves the actual original-norm source operator equation. -/
theorem source_classical_interval_equation_transfer (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    sourceOperator (by simp) (sourceDirichletPotentialCoefficients φ hφ) (sourceClassicalIntervalExtension b f hf) =
      z • sourceDomainInclusion (sourceClassicalIntervalExtension b f hf) := by
  change (CoeffPair.toMax 2).symm
    (operator (by simp) ((CoeffPair.toMax 2) ((CoeffPair.toMax 2).symm (dirichletPotentialCoefficients φ hφ)))
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalIntervalExtension b f hf)))) =
    z • (CoeffPair.toMax 2).symm (domainInclusion
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalIntervalExtension b f hf))))
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [classical_interval_equation_transfer b φ f hφ hf z h, map_smul]

/-- The paragraph following Lemma 4.1: the two original interval spectra exhaust the reflected source spectrum. -/
theorem source_periodicSpectrum_eq_classicalEigenvalues_union (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    (sourceResolventSet (by simp) (sourceDirichletPotentialCoefficients φ hφ))ᶜ =
      classicalEigenvalues .dirichlet φ ∪ classicalEigenvalues .neumann φ := by
  rw [sourceResolventSet_eq]
  change (resolventSet (by simp) ((CoeffPair.toMax 2)
    ((CoeffPair.toMax 2).symm (dirichletPotentialCoefficients φ hφ))))ᶜ = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact periodicSpectrum_eq_classicalEigenvalues_union φ hφ

/-- Original-norm extensions retain the physical normalized Fourier integrals. -/
theorem sourceClassicalIntervalExtension_coefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (n : ℤ) :
    (sourceClassicalIntervalExtension b f hf).fst.val n =
      periodTwoCoefficient (fun x => (intervalExtension b f x).1) n ∧
    (sourceClassicalIntervalExtension b f hf).snd.val n =
      periodTwoCoefficient (fun x => (intervalExtension b f x).2) n := by
  exact ⟨classicalIntervalExtension_fst b f hf n, classicalIntervalExtension_snd b f hf n⟩

/-- The actual circle representative of the original-norm extension. -/
def sourceClassicalCircleExtension (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) : C(AddCircle (2 : ℝ), ℂ) × C(AddCircle (2 : ℝ), ℂ) :=
  (sobolevSynthesis (by simp) (sourceClassicalIntervalExtension b f hf).fst,
    sobolevSynthesis (by simp) (sourceClassicalIntervalExtension b f hf).snd)

theorem sourceClassicalCircleExtension_regular (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    HasPeriodicH1Regularity (sourceClassicalCircleExtension b f hf).1 ∧
      HasPeriodicH1Regularity (sourceClassicalCircleExtension b f hf).2 :=
  ⟨hasPeriodicH1Regularity_sobolevSynthesis _, hasPeriodicH1Regularity_sobolevSynthesis _⟩

theorem sourceClassicalCircleExtension_reconstruct (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    EqOn (fun x : ℝ => ((sourceClassicalCircleExtension b f hf).1 (x : AddCircle (2 : ℝ)),
      (sourceClassicalCircleExtension b f hf).2 (x : AddCircle (2 : ℝ)))) (intervalExtension b f) (Icc 0 2) :=
  fun _ hx => classicalIntervalExtension_reconstruct b f hf hx

/-- Lemma 4.1 with actual periodic H¹ representatives and the actual reflected equation. -/
theorem sourceLemma4_1 (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    ∃ F : C(AddCircle (2 : ℝ), ℂ) × C(AddCircle (2 : ℝ), ℂ),
      HasPeriodicH1Regularity F.1 ∧ HasPeriodicH1Regularity F.2 ∧
      EqOn (fun x : ℝ => (F.1 (x : AddCircle (2 : ℝ)), F.2 (x : AddCircle (2 : ℝ))))
        (intervalExtension b f) (Icc 0 2) ∧
      physicalOperator (intervalExtension .dirichlet φ)
        (fun x : ℝ => (F.1 (x : AddCircle (2 : ℝ)), F.2 (x : AddCircle (2 : ℝ))))
        =ᵐ[volume.restrict (Ioc 0 2)]
        (fun x : ℝ => z • (F.1 (x : AddCircle (2 : ℝ)), F.2 (x : AddCircle (2 : ℝ)))) := by
  let F := sourceClassicalCircleExtension b f hf
  have hr := sourceClassicalCircleExtension_regular b f hf
  have he := sourceClassicalCircleExtension_reconstruct b f hf
  refine ⟨F,hr.1,hr.2,he,?_⟩
  have ho := physicalOperator_congr_on_period (Filter.EventuallyEq.rfl (f := intervalExtension .dirichlet φ)) he
  have ht := physical_interval_equation_transfer b φ f hf z h
  filter_upwards [ho,ht,ae_restrict_mem measurableSet_Ioc] with x hx hy hm
  exact (hx.trans hy).trans (congrArg (fun u => z • u) (he (Ioc_subset_Icc_self hm)).symm)

/-- The source potential coefficients are exactly the normalized physical Fourier integrals. -/
theorem sourceDirichletPotentialCoefficients_coefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (sourceDirichletPotentialCoefficients φ hφ).fst n =
      periodTwoCoefficient (fun x => (intervalExtension .dirichlet φ x).1) n ∧
    (sourceDirichletPotentialCoefficients φ hφ).snd n =
      periodTwoCoefficient (fun x => (intervalExtension .dirichlet φ x).2) n := ⟨rfl,rfl⟩

/-- Physical synthesis recovers the actual Dirichlet-reflected potential almost everywhere. -/
theorem sourceDirichletPotentialCoefficients_reconstruct (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    physicalBase (CoeffPair.toMax 2 (sourceDirichletPotentialCoefficients φ hφ))
      =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension .dirichlet φ := by
  unfold sourceDirichletPotentialCoefficients
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact physicalBase_dirichletPotentialCoefficients φ hφ

/-- The original-norm extension retains every value on [0,1], including both endpoints. -/
theorem sourceClassicalCircleExtension_restrict (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) {x : ℝ} (hx : x ∈ Icc 0 1) :
    ((sourceClassicalCircleExtension b f hf).1 (x : AddCircle (2 : ℝ)),
      (sourceClassicalCircleExtension b f hf).2 (x : AddCircle (2 : ℝ))) = f x :=
  classicalIntervalExtension_restrict b f hf hx

/-- Nonzero original eigenfunctions give nonzero vectors in the original weighted source space. -/
theorem sourceClassicalIntervalExtension_ne_zero (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (hne : ¬ EqOn f 0 (Icc 0 1)) :
    sourceClassicalIntervalExtension b f hf ≠ 0 := by
  intro h
  apply classicalIntervalExtension_ne_zero b f hf hne
  have he := congrArg (WeightedCoeffPair.toMax (Weight.sobolev 1) 2) h
  simpa only [sourceClassicalIntervalExtension, ContinuousLinearEquiv.apply_symm_apply, map_zero] using he

/-- Both original boundary problems produce actual nonzero source eigenvectors. -/
theorem source_classical_interval_eigenvector_transfer (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (hne : ¬ EqOn f 0 (Icc 0 1))
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    ∃ a : WeightedCoeffPair (Weight.sobolev 1) 2, a ≠ 0 ∧
      sourceOperator (by simp) (sourceDirichletPotentialCoefficients φ hφ) a = z • sourceDomainInclusion a :=
  ⟨sourceClassicalIntervalExtension b f hf, sourceClassicalIntervalExtension_ne_zero b f hf hne,
    source_classical_interval_equation_transfer b φ f hφ hf z h⟩

/-- Every original boundary eigenvalue lies in the actual source spectrum. -/
theorem source_classical_interval_eigenvalue_mem_spectrum (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) (z : ℂ)
    (hne : ¬ EqOn f 0 (Icc 0 1))
    (h : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    z ∈ (sourceResolventSet (by simp) (sourceDirichletPotentialCoefficients φ hφ))ᶜ := by
  rw [source_periodicSpectrum_eq_classicalEigenvalues_union]
  cases b
  · exact Or.inl ⟨f,hf,hne,h⟩
  · exact Or.inr ⟨f,hf,hne,h⟩

end NLS.ZakharovShabat
