import NLS.ZakharovShabat.SourceParityOperatorDomain
import NLS.ZakharovShabat.SourceLemma3_6

/-! # The actual source operator and inverse on each separate parity space -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceResolventToDomain_mem_sourceDomainParitySubspace
    (hp : p ≠ ⊤) (φ : CoeffPair p) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (hz : z ∈ sourceResolventSet hp φ)
    (a : CoeffPair p) (ha : a ∈ sourceParitySubspace r) :
    sourceResolventToDomain hp φ z a ∈ sourceDomainParitySubspace r := by
  change (WeightedCoeffPair.toMax (Weight.sobolev 1) p)
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm
      (resolventToDomain hp (CoeffPair.toMax p φ) z (CoeffPair.toMax p a))) ∈ domainParitySubspace (p := p) r
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact resolventToDomain_mem_domainParitySubspace hp _ hφ r z
    (by rwa [sourceResolventSet_eq] at hz) _ ha

/-- Restriction of the original source expression to a single invariant parity. -/
def sourceParityOperator (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    sourceDomainParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r :=
  ((sourceOperator hp φ).comp (sourceDomainParitySubspace (p := p) r).subtypeL).codRestrict (sourceParitySubspace (p := p) r)
    (fun a => sourceOperator_mem_sourceParitySubspace hp φ hφ r a.val a.property)

@[simp] theorem sourceParityOperator_coe (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (a : sourceDomainParitySubspace (p := p) r) :
    (sourceParityOperator hp φ hφ r a : CoeffPair p) = sourceOperator hp φ a := rfl

/-- Each parity has its own densely defined unbounded operator on its own base space. -/
def sourceParityUnboundedOperator (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    sourceParitySubspace (p := p) r →ₗ.[ℂ] sourceParitySubspace (p := p) r where
  domain := LinearMap.range (sourceParityDomainInclusion r).toLinearMap
  toFun := (sourceParityOperator hp φ hφ r).toLinearMap.comp
    (sourceParityUnboundedDomainEquiv r).symm.toLinearMap

theorem sourceParityUnboundedOperator_dense_domain (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    Dense ((sourceParityUnboundedOperator hp φ hφ r).domain : Set (sourceParitySubspace (p := p) r)) :=
  sourceParityDomainInclusion_denseRange hp r

@[simp] theorem sourceParityUnboundedOperator_apply (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (a : sourceDomainParitySubspace (p := p) r) :
    sourceParityUnboundedOperator hp φ hφ r (sourceParityUnboundedDomainEquiv r a) =
      sourceParityOperator hp φ hφ r a := by
  change sourceParityOperator hp φ hφ r
    ((sourceParityUnboundedDomainEquiv r).symm (sourceParityUnboundedDomainEquiv r a)) = _
  rw [LinearEquiv.symm_apply_apply]

def sourceParitySpectralPencil (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) :
    sourceDomainParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r :=
  z • sourceParityDomainInclusion r - sourceParityOperator hp φ hφ r

theorem sourceParitySpectralPencil_coe (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (a : sourceDomainParitySubspace (p := p) r) :
    (sourceParitySpectralPencil hp φ hφ r z a : CoeffPair p) = sourceSpectralPencil hp φ z a := by
  rw [sourceSpectralPencil_eq]
  rfl

/-- The original full inverse preserves the exact one-derivative parity domain. -/
def sourceParityResolventToDomain (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceResolventSet hp φ) :
    sourceParitySubspace (p := p) r →L[ℂ] sourceDomainParitySubspace (p := p) r :=
  ((sourceResolventToDomain hp φ z).comp (sourceParitySubspace (p := p) r).subtypeL).codRestrict (sourceDomainParitySubspace (p := p) r)
    (fun a => sourceResolventToDomain_mem_sourceDomainParitySubspace hp φ hφ r z hz a.val a.property)

theorem sourceParitySpectralPencil_resolvent (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceResolventSet hp φ) (a : sourceParitySubspace (p := p) r) :
    sourceParitySpectralPencil hp φ hφ r z (sourceParityResolventToDomain hp φ hφ r z hz a) = a := by
  apply Subtype.ext
  rw [sourceParitySpectralPencil_coe]
  exact sourceSpectralPencil_sourceResolventToDomain hp φ z hz a

theorem sourceParityResolvent_spectralPencil (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceResolventSet hp φ) (a : sourceDomainParitySubspace (p := p) r) :
    sourceParityResolventToDomain hp φ hφ r z hz (sourceParitySpectralPencil hp φ hφ r z a) = a := by
  apply Subtype.ext
  change sourceResolventToDomain hp φ z (sourceParitySpectralPencil hp φ hφ r z a) = (a : WeightedCoeffPair _ p)
  rw [sourceParitySpectralPencil_coe]
  exact sourceResolventToDomain_sourceSpectralPencil hp φ z hz a

end NLS.ZakharovShabat
