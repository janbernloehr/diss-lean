import NLS.ZakharovShabat.SourceParitySelfAdjoint
import NLS.ZakharovShabat.PhysicalPeriodicSelfAdjoint

/-! # Separate physical Hilbert realizations of the two boundary sectors -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual Fourier image of one parity inside the physical period-two L² space. -/
def physicalParitySubspace (r : ℤ) : Submodule ℂ SourceCirclePairL2 :=
  (sourceParitySubspace (p := 2) r).map sourceCircleSynthesis.toLinearEquiv.toLinearMap

/-- Fourier synthesis restricts isometrically onto the physical parity space. -/
def sourceParityCircleSynthesis (r : ℤ) :
    sourceParitySubspace (p := 2) r ≃ₗᵢ[ℂ] physicalParitySubspace r :=
  LinearIsometryEquiv.submoduleMap (sourceParitySubspace (p := 2) r) sourceCircleSynthesis

@[simp] theorem sourceParityCircleSynthesis_coe (r : ℤ)
    (a : sourceParitySubspace (p := 2) r) :
    (sourceParityCircleSynthesis r a : SourceCirclePairL2) = sourceCircleSynthesis a.val := rfl

instance physicalParityCompleteSpace (r : ℤ) : CompleteSpace (physicalParitySubspace r) :=
  (sourceParityCircleSynthesis r).toIsometryEquiv.completeSpace_iff.mp inferInstance

def physicalParityDomainInclusion (r : ℤ) :
    sourceDomainParitySubspace (p := 2) r →L[ℂ] physicalParitySubspace r :=
  (sourceParityCircleSynthesis r).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sourceParityDomainInclusion r)

theorem physicalParityDomainInclusion_injective (r : ℤ) :
    Function.Injective (physicalParityDomainInclusion r) :=
  (sourceParityCircleSynthesis r).injective.comp (sourceParityDomainInclusion_injective r)

theorem physicalParityDomainInclusion_denseRange (r : ℤ) :
    DenseRange (physicalParityDomainInclusion r) :=
  (sourceParityCircleSynthesis r).surjective.denseRange.comp
    (sourceParityDomainInclusion_denseRange (by simp) r) (sourceParityCircleSynthesis r).continuous

def physicalParityDomainEquiv (r : ℤ) : sourceDomainParitySubspace (p := 2) r ≃ₗ[ℂ]
    LinearMap.range (physicalParityDomainInclusion r).toLinearMap :=
  LinearEquiv.ofInjective (physicalParityDomainInclusion r).toLinearMap
    (physicalParityDomainInclusion_injective r)

/-- The signed physical expression on exactly one included parity domain. -/
def physicalParityOperator (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    physicalParitySubspace r →ₗ.[ℂ] physicalParitySubspace r where
  domain := LinearMap.range (physicalParityDomainInclusion r).toLinearMap
  toFun := (sourceParityCircleSynthesis r).toLinearEquiv.toLinearMap.comp
    ((sourceParityOperator (by simp) φ hφ r).toLinearMap.comp
      (physicalParityDomainEquiv r).symm.toLinearMap)

@[simp] theorem physicalParityDomainEquiv_coe (r : ℤ)
    (a : sourceDomainParitySubspace (p := 2) r) :
    (physicalParityDomainEquiv r a : physicalParitySubspace r) =
      sourceParityCircleSynthesis r (sourceParityDomainInclusion r a) := rfl

@[simp] theorem physicalParityOperator_apply (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (a : sourceDomainParitySubspace (p := 2) r) :
    physicalParityOperator φ hφ r (physicalParityDomainEquiv r a) =
      sourceParityCircleSynthesis r (sourceParityOperator (by simp) φ hφ r a) := by
  change sourceParityCircleSynthesis r (sourceParityOperator (by simp) φ hφ r
    ((physicalParityDomainEquiv r).symm (physicalParityDomainEquiv r a))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem physicalParityOperator_formal_symmetric (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (hreal : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    (physicalParityOperator φ hφ r).IsFormalAdjoint (physicalParityOperator φ hφ r) := by
  intro x y
  obtain ⟨a,rfl⟩ := (physicalParityDomainEquiv r).surjective x
  obtain ⟨b,rfl⟩ := (physicalParityDomainEquiv r).surjective y
  simpa only [physicalParityOperator_apply,physicalParityDomainEquiv_coe,
    (sourceParityCircleSynthesis r).inner_map_map,Submodule.coe_inner,
    sourceParityOperator_coe,sourceParityDomainInclusion_coe] using sourceOperator_inner_symmetric φ hreal a b

set_option backward.isDefEq.respectTransparency false in
theorem physicalParityOperator_pencil_surjective (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceResolventSet (by simp) φ) :
    Function.Surjective (linearPMapPencil (physicalParityOperator φ hφ r) z) := by
  intro y
  let a := sourceParityResolventToDomain (by simp) φ hφ r z hz
    ((sourceParityCircleSynthesis r).symm y)
  refine ⟨physicalParityDomainEquiv r a,?_⟩
  rw [linearPMapPencil_apply,physicalParityDomainEquiv_coe,physicalParityOperator_apply,
    ← map_smul,← map_sub]
  have he : z • sourceParityDomainInclusion r a - sourceParityOperator (by simp) φ hφ r a =
      (sourceParityCircleSynthesis r).symm y :=
    sourceParitySpectralPencil_resolvent (by simp) φ hφ r z hz _
  rw [he,LinearIsometryEquiv.apply_symm_apply]

/-- Equality with the actual Hilbert adjoint on each physical parity space, including domains. -/
theorem physicalParityOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (hreal : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    IsSelfAdjoint (physicalParityOperator φ hφ r) := by
  apply isSelfAdjoint_of_conjugate_pencils_surjective (physicalParityOperator φ hφ r)
    (physicalParityDomainInclusion_denseRange r)
    (physicalParityOperator_formal_symmetric φ hφ hreal r) Complex.I
  · apply physicalParityOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hreal _ (by simp)
  · apply physicalParityOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hreal _ (by simp)

/-- Each restricted domain has the original continuous physical representative. -/
theorem physicalParityDomain_representative (r : ℤ)
    (a : sourceDomainParitySubspace (p := 2) r) :
    sourceCircleRepresentative (physicalParityDomainInclusion r a : SourceCirclePairL2)
      =ᵐ[volume.restrict (Ioc 0 2)]
      physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a.val) :=
  physicalBase_domainInclusion _

/-- Restriction retains the original differential expression for arbitrary even L² potentials. -/
theorem physicalParityOperator_representative (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (a : sourceDomainParitySubspace (p := 2) r) :
    sourceCircleRepresentative (physicalParityOperator φ hφ r (physicalParityDomainEquiv r a) : SourceCirclePairL2)
      =ᵐ[volume.restrict (Ioc 0 2)]
      physicalOperator (physicalBase (CoeffPair.toMax 2 φ))
        (physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a.val)) := by
  rw [physicalParityOperator_apply,sourceParityCircleSynthesis_coe,sourceParityOperator_coe]
  exact physical_operator_realization _ _

/-- An original period-one real potential gives both separate physical self-adjoint operators. -/
theorem sourcePhysicalParityOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    IsSelfAdjoint (physicalParityOperator (periodOnePair φ) (periodOnePotential_mem φ) r) :=
  physicalParityOperator_isSelfAdjoint _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ) r

end NLS.ZakharovShabat
