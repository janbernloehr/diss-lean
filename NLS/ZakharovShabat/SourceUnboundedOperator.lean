import NLS.ZakharovShabat.SourceResolvent
import Mathlib.LinearAlgebra.LinearPMap

/-! # The actual periodic operator in the original component-sum source norm -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceDomainInclusion_injective :
    Function.Injective (sourceDomainInclusion (p := p)) := by
  change Function.Injective ((CoeffPair.toMax p).symm ∘ domainInclusion ∘
    WeightedCoeffPair.toMax (Weight.sobolev 1) p)
  exact (CoeffPair.toMax p).symm.injective.comp
    (domainInclusion_injective.comp (WeightedCoeffPair.toMax (Weight.sobolev 1) p).injective)

theorem sourceDomainInclusion_denseRange (hp : p ≠ ⊤) :
    DenseRange (sourceDomainInclusion (p := p)) := by
  change DenseRange ((CoeffPair.toMax p).symm ∘ domainInclusion ∘
    WeightedCoeffPair.toMax (Weight.sobolev 1) p)
  exact (CoeffPair.toMax p).symm.surjective.denseRange.comp
    ((domainInclusion_denseRange hp).comp
      (WeightedCoeffPair.toMax (Weight.sobolev 1) p).surjective.denseRange
      domainInclusion.continuous) (CoeffPair.toMax p).symm.continuous

/-- The original one-derivative domain is identified with its actual image in the base space. -/
def sourceUnboundedDomainEquiv : WeightedCoeffPair (Weight.sobolev 1) p ≃ₗ[ℂ]
    LinearMap.range (sourceDomainInclusion (p := p)).toLinearMap :=
  LinearEquiv.ofInjective (sourceDomainInclusion (p := p)).toLinearMap sourceDomainInclusion_injective

/-- The source operator as an unbounded operator with the unchanged one-derivative domain. -/
def sourceUnboundedOperator (hp : p ≠ ⊤) (φ : CoeffPair p) : CoeffPair p →ₗ.[ℂ] CoeffPair p where
  domain := LinearMap.range sourceDomainInclusion.toLinearMap
  toFun := (sourceOperator hp φ).toLinearMap.comp sourceUnboundedDomainEquiv.symm.toLinearMap

theorem sourceUnboundedOperator_dense_domain (hp : p ≠ ⊤) (φ : CoeffPair p) :
    Dense ((sourceUnboundedOperator hp φ).domain : Set (CoeffPair p)) :=
  sourceDomainInclusion_denseRange hp

@[simp] theorem sourceUnboundedOperator_apply (hp : p ≠ ⊤) (φ : CoeffPair p)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceUnboundedOperator hp φ (sourceUnboundedDomainEquiv a) = sourceOperator hp φ a := by
  change sourceOperator hp φ (sourceUnboundedDomainEquiv.symm (sourceUnboundedDomainEquiv a)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem sourceUnboundedDomainEquiv_coe (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    (sourceUnboundedDomainEquiv a : CoeffPair p) = sourceDomainInclusion a := rfl

/-- Membership retains precisely the source one-derivative regularity, independently of the potential. -/
theorem mem_sourceUnboundedOperator_domain (hp : p ≠ ⊤) (φ : CoeffPair p) (x : CoeffPair p) :
    x ∈ (sourceUnboundedOperator hp φ).domain ↔
      ∃ a : WeightedCoeffPair (Weight.sobolev 1) p, sourceDomainInclusion a = x := Iff.rfl

end NLS.ZakharovShabat
