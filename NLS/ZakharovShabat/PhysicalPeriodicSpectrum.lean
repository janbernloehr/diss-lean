import NLS.ZakharovShabat.ClassicalSignedEigenvalues
import NLS.ZakharovShabat.PhysicalPeriodicSelfAdjoint

/-! # Bounded-inverse spectrum of the actual physical period-two operator -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual physical period-two pencil is intertwined with the original source pencil. -/
theorem physicalPeriodicPencil_intertwining (φ : CoeffPair 2) (z : ℂ)
    (a : WeightedCoeffPair (Weight.sobolev 1) 2) :
    linearPMapPencil (physicalPeriodicOperator φ) z (physicalPeriodicDomainEquiv a) =
      sourceCircleSynthesis (sourceSpectralPencil (by simp) φ z a) := by
  rw [linearPMapPencil_apply,physicalPeriodicDomainEquiv_coe,physicalPeriodicOperator_apply,
    sourceSpectralPencil_eq]
  change z • sourceCircleSynthesis (sourceDomainInclusion a) - sourceCircleSynthesis (sourceOperator (by simp) φ a) =
    sourceCircleSynthesis (z • sourceDomainInclusion a-sourceOperator (by simp) φ a)
  rw [map_sub,map_smul]

theorem physicalPeriodicPencil_bijective_iff (φ : CoeffPair 2) (z : ℂ) :
    Function.Bijective (linearPMapPencil (physicalPeriodicOperator φ) z) ↔
      z ∈ sourceResolventSet (by simp) φ := by
  have he : linearPMapPencil (physicalPeriodicOperator φ) z ∘ physicalPeriodicDomainEquiv =
      sourceCircleSynthesis ∘ sourceSpectralPencil (by simp) φ z :=
    funext (physicalPeriodicPencil_intertwining φ z)
  rw [← Function.Bijective.of_comp_iff _ physicalPeriodicDomainEquiv.bijective,he,
    Function.Bijective.of_comp_iff' sourceCircleSynthesis.bijective]
  rfl

/-- The actual physical period-two resolvent set is defined by bounded two-sided inverse on its full H¹ domain. -/
def physicalPeriodicResolventSet (φ : CoeffPair 2) : Set ℂ :=
  {z | ∃ R : SourceCirclePairL2 →L[ℂ] (physicalPeriodicOperator φ).domain,
    (∀ f, linearPMapPencil (physicalPeriodicOperator φ) z (R f) = f) ∧
    (∀ g, R (linearPMapPencil (physicalPeriodicOperator φ) z g) = g)}

/-- Continuous inclusion from the original weighted norm into the actual physical domain. -/
def physicalPeriodicDomainEmbedding : WeightedCoeffPair (Weight.sobolev 1) 2 →L[ℂ]
    LinearMap.range physicalPeriodicDomainInclusion.toLinearMap :=
  physicalPeriodicDomainInclusion.codRestrict _ (fun a => ⟨a,rfl⟩)

/-- The actual physical inverse with values in the full period-two domain. -/
def physicalPeriodicResolventToDomain (φ : CoeffPair 2) (z : ℂ) :
    SourceCirclePairL2 →L[ℂ] (physicalPeriodicOperator φ).domain :=
  physicalPeriodicDomainEmbedding.comp ((sourceResolventToDomain (by simp) φ z).comp
    sourceCircleSynthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem physicalPeriodicPencil_resolvent (φ : CoeffPair 2) (z : ℂ)
    (hz : z ∈ sourceResolventSet (by simp) φ) (f : SourceCirclePairL2) :
    linearPMapPencil (physicalPeriodicOperator φ) z (physicalPeriodicResolventToDomain φ z f) = f := by
  change linearPMapPencil (physicalPeriodicOperator φ) z (physicalPeriodicDomainEquiv
    (sourceResolventToDomain (by simp) φ z (sourceCircleSynthesis.symm f))) = f
  rw [physicalPeriodicPencil_intertwining,sourceSpectralPencil_sourceResolventToDomain _ _ _ hz,
    LinearIsometryEquiv.apply_symm_apply]

theorem physicalPeriodicResolvent_pencil (φ : CoeffPair 2) (z : ℂ)
    (hz : z ∈ sourceResolventSet (by simp) φ) (f : (physicalPeriodicOperator φ).domain) :
    physicalPeriodicResolventToDomain φ z (linearPMapPencil (physicalPeriodicOperator φ) z f) = f := by
  obtain ⟨a,rfl⟩ := physicalPeriodicDomainEquiv.surjective f
  rw [physicalPeriodicPencil_intertwining]
  change physicalPeriodicDomainEquiv (sourceResolventToDomain (by simp) φ z
    (sourceCircleSynthesis.symm (sourceCircleSynthesis (sourceSpectralPencil (by simp) φ z a)))) =
      physicalPeriodicDomainEquiv a
  rw [LinearIsometryEquiv.symm_apply_apply,sourceResolventToDomain_sourceSpectralPencil _ _ _ hz]

/-- The physical and coefficient realizations have the same full bounded-inverse resolvent set. -/
theorem mem_physicalPeriodicResolventSet_iff (φ : CoeffPair 2) (z : ℂ) :
    z ∈ physicalPeriodicResolventSet φ ↔ z ∈ sourceResolventSet (by simp) φ := by
  constructor
  · rintro ⟨R,h₁,h₂⟩
    exact (physicalPeriodicPencil_bijective_iff φ z).mp
      ⟨Function.LeftInverse.injective h₂,Function.RightInverse.surjective h₁⟩
  · intro hz
    exact ⟨physicalPeriodicResolventToDomain φ z,physicalPeriodicPencil_resolvent φ z hz,
      physicalPeriodicResolvent_pencil φ z hz⟩

/-- The actual physical period-two base-space resolvent. -/
def physicalPeriodicResolvent (φ : CoeffPair 2) (z : ℂ) : SourceCirclePairL2 →L[ℂ] SourceCirclePairL2 :=
  (physicalPeriodicOperator φ).domain.subtypeL.comp (physicalPeriodicResolventToDomain φ z)

theorem physicalPeriodicResolvent_eq_conjugate (φ : CoeffPair 2) (z : ℂ) :
    physicalPeriodicResolvent φ z = sourceCircleSynthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((sourceResolvent (by simp) φ z).comp sourceCircleSynthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  rw [sourceResolvent_eq_inclusion_comp]
  ext f : 1
  rfl

theorem isCompactOperator_physicalPeriodicResolvent (φ : CoeffPair 2) (z : ℂ) :
    IsCompactOperator (physicalPeriodicResolvent φ z) := by
  rw [physicalPeriodicResolvent_eq_conjugate]
  exact ((isCompactOperator_sourceResolvent (by simp) φ z).comp_clm
    sourceCircleSynthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      sourceCircleSynthesis.toContinuousLinearEquiv.toContinuousLinearMap

/-- The actual physical period-two spectrum is the complement of bounded invertibility. -/
def physicalPeriodicSpectrum (φ : CoeffPair 2) : Set ℂ := (physicalPeriodicResolventSet φ)ᶜ

theorem physicalPeriodicSpectrum_eq (φ : CoeffPair 2) :
    physicalPeriodicSpectrum φ = periodicSpectrum (by simp) (CoeffPair.toMax 2 φ) := by
  have he : physicalPeriodicResolventSet φ = sourceResolventSet (by simp) φ :=
    Set.ext (mem_physicalPeriodicResolventSet_iff φ)
  rw [physicalPeriodicSpectrum,he,sourceResolventSet_eq]
  rfl

/-- The literal physical period-two spectrum equals the union of both actual classical signed spectra. -/
theorem physicalPeriodicSpectrum_eq_classicalSigned_union (u : IntervalPairL2) :
    physicalPeriodicSpectrum (periodOnePair (sourcePhysicalL2Equiv.symm u)) =
      classicalSignedSpectrum u 0 ∪ classicalSignedSpectrum u 1 := by
  rw [physicalPeriodicSpectrum_eq,classicalSignedSpectrum_union_eq_periodic]
  rfl

/-- The same physical period-two spectrum is exactly the two full classical ODE eigenvalue sets. -/
theorem physicalPeriodicSpectrum_eq_classicalSignedEigenvalues_union (u : IntervalPairL2) :
    physicalPeriodicSpectrum (periodOnePair (sourcePhysicalL2Equiv.symm u)) =
      classicalSignedEigenvalues u 0 ∪ classicalSignedEigenvalues u 1 := by
  rw [physicalPeriodicSpectrum_eq_classicalSigned_union,classicalSignedSpectrum_eq_eigenvalues,
    classicalSignedSpectrum_eq_eigenvalues]

end NLS.ZakharovShabat
