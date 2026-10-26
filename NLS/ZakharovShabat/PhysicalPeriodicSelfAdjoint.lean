import NLS.ZakharovShabat.SourcePeriodicSelfAdjoint
import NLS.ZakharovShabat.SourceBoundaryFourier
import NLS.ZakharovShabat.FiniteSourceRealization

/-! # The self-adjoint physical period-two realization -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

instance sourceCirclePairL2InnerProductSpace : InnerProductSpace ℂ SourceCirclePairL2 :=
  inferInstanceAs (InnerProductSpace ℂ (WithLp 2 (Fourier.CircleL2 × Fourier.CircleL2)))

instance sourceCirclePairL2CompleteSpace : CompleteSpace SourceCirclePairL2 :=
  inferInstanceAs (CompleteSpace (WithLp 2 (Fourier.CircleL2 × Fourier.CircleL2)))

/-- The physical domain consists of the actual Fourier synthesis of the original H¹ coefficients. -/
def physicalPeriodicDomainInclusion : WeightedCoeffPair (Weight.sobolev 1) 2 →L[ℂ] SourceCirclePairL2 :=
  sourceCircleSynthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp sourceDomainInclusion

theorem physicalPeriodicDomainInclusion_injective : Function.Injective physicalPeriodicDomainInclusion :=
  sourceCircleSynthesis.injective.comp sourceDomainInclusion_injective

theorem physicalPeriodicDomainInclusion_denseRange : DenseRange physicalPeriodicDomainInclusion :=
  sourceCircleSynthesis.surjective.denseRange.comp
    (sourceDomainInclusion_denseRange (by simp)) sourceCircleSynthesis.continuous

def physicalPeriodicDomainEquiv : WeightedCoeffPair (Weight.sobolev 1) 2 ≃ₗ[ℂ]
    LinearMap.range physicalPeriodicDomainInclusion.toLinearMap :=
  LinearEquiv.ofInjective physicalPeriodicDomainInclusion.toLinearMap
    physicalPeriodicDomainInclusion_injective

/-- The original signed physical differential operator with its full periodic H¹ domain. -/
def physicalPeriodicOperator (φ : CoeffPair 2) : SourceCirclePairL2 →ₗ.[ℂ] SourceCirclePairL2 where
  domain := LinearMap.range physicalPeriodicDomainInclusion.toLinearMap
  toFun := sourceCircleSynthesis.toLinearEquiv.toLinearMap.comp
    ((sourceOperator (by simp) φ).toLinearMap.comp physicalPeriodicDomainEquiv.symm.toLinearMap)

@[simp] theorem physicalPeriodicDomainEquiv_coe (a : WeightedCoeffPair (Weight.sobolev 1) 2) :
    (physicalPeriodicDomainEquiv a : SourceCirclePairL2) =
      sourceCircleSynthesis (sourceDomainInclusion a) := rfl

@[simp] theorem physicalPeriodicOperator_apply (φ : CoeffPair 2)
    (a : WeightedCoeffPair (Weight.sobolev 1) 2) :
    physicalPeriodicOperator φ (physicalPeriodicDomainEquiv a) =
      sourceCircleSynthesis (sourceOperator (by simp) φ a) := by
  change sourceCircleSynthesis (sourceOperator (by simp) φ
    (physicalPeriodicDomainEquiv.symm (physicalPeriodicDomainEquiv a))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem physicalPeriodicOperator_formal_symmetric (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    (physicalPeriodicOperator φ).IsFormalAdjoint (physicalPeriodicOperator φ) := by
  intro x y
  obtain ⟨a,rfl⟩ := physicalPeriodicDomainEquiv.surjective x
  obtain ⟨b,rfl⟩ := physicalPeriodicDomainEquiv.surjective y
  simpa only [physicalPeriodicOperator_apply,physicalPeriodicDomainEquiv_coe,
    sourceCircleSynthesis.inner_map_map] using sourceOperator_inner_symmetric φ hφ a b

set_option backward.isDefEq.respectTransparency false in
theorem physicalPeriodicOperator_pencil_surjective (φ : CoeffPair 2) (z : ℂ)
    (hz : z ∈ sourceResolventSet (by simp) φ) :
    Function.Surjective (linearPMapPencil (physicalPeriodicOperator φ) z) := by
  intro y
  let a := sourceResolventToDomain (by simp) φ z (sourceCircleSynthesis.symm y)
  refine ⟨physicalPeriodicDomainEquiv a,?_⟩
  rw [linearPMapPencil_apply,physicalPeriodicDomainEquiv_coe,physicalPeriodicOperator_apply,
    ← map_smul,← map_sub]
  have h := sourceSpectralPencil_sourceResolventToDomain (by simp) φ z hz
    (sourceCircleSynthesis.symm y)
  have he : z • sourceDomainInclusion a - sourceOperator (by simp) φ a =
      sourceCircleSynthesis.symm y := by
    simpa only [sourceSpectralPencil_eq,sub_apply,smul_apply] using h
  rw [he,LinearIsometryEquiv.apply_symm_apply]

/-- Self-adjointness on the actual physical Hilbert space, with its full domain unchanged. -/
theorem physicalPeriodicOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) : IsSelfAdjoint (physicalPeriodicOperator φ) := by
  apply isSelfAdjoint_of_conjugate_pencils_surjective (physicalPeriodicOperator φ)
    physicalPeriodicDomainInclusion_denseRange
    (physicalPeriodicOperator_formal_symmetric φ hφ) Complex.I
  · apply physicalPeriodicOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hφ _ (by simp)
  · apply physicalPeriodicOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hφ _ (by simp)

/-- Domain elements retain their actual continuous one-derivative representatives. -/
theorem physicalPeriodicDomain_representative (a : WeightedCoeffPair (Weight.sobolev 1) 2) :
    sourceCircleRepresentative (physicalPeriodicDomainInclusion a) =ᵐ[volume.restrict (Ioc 0 2)]
      physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) :=
  physicalBase_domainInclusion _

/-- The operator acts by the original differential expression almost everywhere, for every L² potential. -/
theorem physicalPeriodicOperator_representative (φ : CoeffPair 2)
    (a : WeightedCoeffPair (Weight.sobolev 1) 2) :
    sourceCircleRepresentative (physicalPeriodicOperator φ (physicalPeriodicDomainEquiv a))
      =ᵐ[volume.restrict (Ioc 0 2)]
      physicalOperator (physicalBase (CoeffPair.toMax 2 φ))
        (physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a)) := by
  rw [physicalPeriodicOperator_apply]
  exact physical_operator_realization _ _

/-- The page 17 periodic realization for an original period-one real Hilbert potential. -/
theorem sourcePhysicalPeriodicOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    IsSelfAdjoint (physicalPeriodicOperator (periodOnePair φ)) :=
  physicalPeriodicOperator_isSelfAdjoint _ (isRealType_periodOnePotential φ hφ)

end NLS.ZakharovShabat
