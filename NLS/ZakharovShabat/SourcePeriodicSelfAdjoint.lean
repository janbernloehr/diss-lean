import NLS.ZakharovShabat.SourceUnboundedOperator
import NLS.ZakharovShabat.RealType
import NLS.FunctionalAnalysis.ConjugatePencilSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Self-adjointness of the actual periodic Hilbert source operator -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal ComplexConjugate
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The existing coefficient duality is the actual original Hilbert inner product. -/
theorem sourceDomainInclusion_inner (a : WeightedCoeffPair (Weight.sobolev 1) 2)
    (b : CoeffPair 2) :
    inner ℂ (sourceDomainInclusion a) b =
      domainPairing (by simp) (CoeffPair.toMax 2 b)
        (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a) := by
  simp only [WithLp.prod_inner_apply,lp.inner_eq_tsum,RCLike.inner_apply,
    domainPairing,Coeff.pairing,WeightedCoeff.sobolevToL1CLM_apply]
  change (∑' n : ℤ, b.fst n * conj ((sourceDomainInclusion a).fst n)) +
      (∑' n : ℤ, b.snd n * conj ((sourceDomainInclusion a).snd n)) =
    (∑' n : ℤ, b.fst n * conj (a.fst.val n)) +
      (∑' n : ℤ, b.snd n * conj (a.snd.val n))
  simp only [sourceDomainInclusion_fst_apply,sourceDomainInclusion_snd_apply]

/-- Symmetry holds in the original component-sum Hilbert norm and exact source domain. -/
theorem sourceOperator_inner_symmetric (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (a b : WeightedCoeffPair (Weight.sobolev 1) 2) :
    inner ℂ (sourceOperator (by simp) φ a) (sourceDomainInclusion b) =
      inner ℂ (sourceDomainInclusion a) (sourceOperator (by simp) φ b) := by
  rw [← inner_conj_symm,sourceDomainInclusion_inner,sourceDomainInclusion_inner]
  change conj (domainPairing (by simp)
    (operator (by simp) (CoeffPair.toMax 2 φ) (WeightedCoeffPair.toMax _ 2 a))
    (WeightedCoeffPair.toMax _ 2 b)) =
    domainPairing (by simp)
    (operator (by simp) (CoeffPair.toMax 2 φ) (WeightedCoeffPair.toMax _ 2 b))
    (WeightedCoeffPair.toMax _ 2 a)
  rw [domainPairing_operator_conj (by simp) _ hφ,starRingEnd_self_apply]

theorem sourceUnboundedOperator_formal_symmetric (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    (sourceUnboundedOperator (by simp) φ).IsFormalAdjoint
      (sourceUnboundedOperator (by simp) φ) := by
  intro x y
  obtain ⟨a,rfl⟩ := sourceUnboundedDomainEquiv.surjective x
  obtain ⟨b,rfl⟩ := sourceUnboundedDomainEquiv.surjective y
  simpa only [sourceUnboundedOperator_apply,sourceUnboundedDomainEquiv_coe] using
    sourceOperator_inner_symmetric φ hφ a b

set_option backward.isDefEq.respectTransparency false in
/-- The existing source resolvent is onto the original partial-operator pencil. -/
theorem sourceUnboundedOperator_pencil_surjective (φ : CoeffPair 2) (z : ℂ)
    (hz : z ∈ sourceResolventSet (by simp) φ) :
    Function.Surjective (linearPMapPencil (sourceUnboundedOperator (by simp) φ) z) := by
  intro y
  refine ⟨sourceUnboundedDomainEquiv (sourceResolventToDomain (by simp) φ z y),?_⟩
  rw [linearPMapPencil_apply,sourceUnboundedDomainEquiv_coe,sourceUnboundedOperator_apply]
  have h := sourceSpectralPencil_sourceResolventToDomain (by simp) φ z hz y
  simpa only [sourceSpectralPencil_eq,sub_apply,
    smul_apply] using h

/-- The original periodic Hilbert operator equals its actual adjoint, including domain equality. -/
theorem sourceUnboundedOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    IsSelfAdjoint (sourceUnboundedOperator (by simp) φ) := by
  apply isSelfAdjoint_of_conjugate_pencils_surjective _
    (sourceUnboundedOperator_dense_domain (by simp) φ)
    (sourceUnboundedOperator_formal_symmetric φ hφ) Complex.I
  · apply sourceUnboundedOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hφ _ (by simp)
  · apply sourceUnboundedOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hφ _ (by simp)

end NLS.ZakharovShabat
