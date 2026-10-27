import NLS.ZakharovShabat.SourceParityUnboundedOperator
import NLS.ZakharovShabat.SourcePeriodicSelfAdjoint
import NLS.ZakharovShabat.PhysicalParity
import NLS.ZakharovShabat.FiniteSourceRealization

/-! # Self-adjointness of each separate source parity operator -/
noncomputable section
set_option autoImplicit false
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

instance sourceParityHilbertCompleteSpace (r : ℤ) :
    CompleteSpace (sourceParitySubspace (p := 2) r) :=
  (isClosed_sourceParitySubspace r).completeSpace_coe

/-- The original Hilbert symmetry restricts to either boundary condition. -/
theorem sourceParityUnboundedOperator_formal_symmetric (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (hreal : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    (sourceParityUnboundedOperator (by simp) φ hφ r).IsFormalAdjoint
      (sourceParityUnboundedOperator (by simp) φ hφ r) := by
  intro x y
  obtain ⟨a,rfl⟩ := (sourceParityUnboundedDomainEquiv r).surjective x
  obtain ⟨b,rfl⟩ := (sourceParityUnboundedDomainEquiv r).surjective y
  simpa only [sourceParityUnboundedOperator_apply,sourceParityUnboundedDomainEquiv_coe,Submodule.coe_inner,
    sourceParityOperator_coe,sourceParityDomainInclusion_coe] using
    sourceOperator_inner_symmetric φ hreal a b

set_option backward.isDefEq.respectTransparency false in
/-- Each full source resolvent supplies an inverse on the exact restricted operator domain. -/
theorem sourceParityUnboundedOperator_pencil_surjective (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceResolventSet (by simp) φ) :
    Function.Surjective (linearPMapPencil (sourceParityUnboundedOperator (by simp) φ hφ r) z) := by
  intro y
  refine ⟨sourceParityUnboundedDomainEquiv r
    (sourceParityResolventToDomain (by simp) φ hφ r z hz y),?_⟩
  rw [linearPMapPencil_apply,sourceParityUnboundedDomainEquiv_coe,
    sourceParityUnboundedOperator_apply]
  exact sourceParitySpectralPencil_resolvent (by simp) φ hφ r z hz y

/-- Each closed parity Hilbert space carries a self-adjoint operator with its own dense H¹ domain. -/
theorem sourceParityUnboundedOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (hreal : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    IsSelfAdjoint (sourceParityUnboundedOperator (by simp) φ hφ r) := by
  apply isSelfAdjoint_of_conjugate_pencils_surjective _
    (sourceParityUnboundedOperator_dense_domain (by simp) φ hφ r)
    (sourceParityUnboundedOperator_formal_symmetric φ hφ hreal r) Complex.I
  · apply sourceParityUnboundedOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hreal _ (by simp)
  · apply sourceParityUnboundedOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hreal _ (by simp)

/-- Both boundary sectors of an original period-one real potential are self-adjoint. -/
theorem sourcePeriodOneParityOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    IsSelfAdjoint (sourceParityUnboundedOperator (by simp) (periodOnePair φ)
      (periodOnePotential_mem φ) r) :=
  sourceParityUnboundedOperator_isSelfAdjoint _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ) r

/-- The actual continuous domain representative satisfies its boundary multiplier. -/
theorem sourceParityDomain_boundary (r : ℤ)
    (a : sourceDomainParitySubspace (p := 2) r) :
    physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) 1 =
      Fourier.wave r 1 • physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) 0 := by
  simpa only [zero_add] using physicalDomain_add_one_of_parity
    (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) r a.property 0

theorem sourceEvenDomain_periodic_boundary (a : sourceDomainParitySubspace (p := 2) 0) :
    physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) 1 =
      physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) 0 := by
  have hw : Fourier.wave 0 1 = 1 := by simp
  simpa only [hw,one_smul] using sourceParityDomain_boundary 0 a

theorem sourceOddDomain_antiperiodic_boundary (a : sourceDomainParitySubspace (p := 2) 1) :
    physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) 1 =
      - physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) 0 := by
  have hw : Fourier.wave 1 1 = -1 := by simpa using Fourier.wave_odd_at_one 0
  simpa only [hw,neg_one_smul] using sourceParityDomain_boundary 1 a

end NLS.ZakharovShabat
