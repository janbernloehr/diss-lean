import NLS.ZakharovShabat.SourceUnboundedOperator
import NLS.ZakharovShabat.SourceParity

/-! # The original one-derivative domain inside each source parity space -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceDomainInclusion_parityProjection (r : ℤ)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceDomainInclusion (sourceDomainParityProjection r a) =
      sourceParityProjection r (sourceDomainInclusion a) := by
  apply (CoeffPair.toMax p).injective
  change domainInclusion ((WeightedCoeffPair.toMax (Weight.sobolev 1) p)
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm
      (domainParityProjection r (WeightedCoeffPair.toMax (Weight.sobolev 1) p a)))) =
    pairParityProjection r (domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))
  rw [ContinuousLinearEquiv.apply_symm_apply,domainInclusion_domainParityProjection]

theorem sourceDomainParityProjection_mem (r : ℤ)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceDomainParityProjection r a ∈ sourceDomainParitySubspace r := by
  rw [mem_sourceDomainParitySubspace,sourceDomainInclusion_parityProjection]
  exact sourceParityProjection_mem r _

/-- The source H¹ inclusion restricted to exactly one Fourier parity, in both original norms. -/
def sourceParityDomainInclusion (r : ℤ) :
    sourceDomainParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r :=
  ((sourceDomainInclusion (p := p)).comp (sourceDomainParitySubspace (p := p) r).subtypeL).codRestrict
    (sourceParitySubspace (p := p) r) (by
      intro a
      change sourceDomainInclusion a.val ∈ sourceParitySubspace r
      exact (mem_sourceDomainParitySubspace (p := p) r a.val).mp a.property)

@[simp] theorem sourceParityDomainInclusion_coe (r : ℤ)
    (a : sourceDomainParitySubspace (p := p) r) :
    (sourceParityDomainInclusion r a : CoeffPair p) = sourceDomainInclusion a := rfl

theorem sourceParityDomainInclusion_injective (r : ℤ) :
    Function.Injective (sourceParityDomainInclusion (p := p) r) := by
  intro a b h
  exact Subtype.ext (sourceDomainInclusion_injective (congrArg Subtype.val h))

/-- Each boundary-domain inclusion is dense in its own source parity Hilbert/Banach space. -/
theorem sourceParityDomainInclusion_denseRange (hp : p ≠ ⊤) (r : ℤ) :
    DenseRange (sourceParityDomainInclusion (p := p) r) := by
  let P : CoeffPair p →L[ℂ] sourceParitySubspace (p := p) r :=
    (sourceParityProjection (p := p) r).codRestrict (sourceParitySubspace (p := p) r) (sourceParityProjection_mem r)
  have hP : Function.Surjective P := by
    intro x
    refine ⟨x,Subtype.ext ?_⟩
    change sourceParityProjection r x.val = x.val
    exact (sourceParityProjection_eq_self_iff (p := p) r x.val).mpr x.property
  have hd := hP.denseRange.comp (sourceDomainInclusion_denseRange hp) P.continuous
  have hr : Set.range (P ∘ sourceDomainInclusion (p := p)) ⊆ Set.range (sourceParityDomainInclusion (p := p) r) := by
    rintro _ ⟨a,rfl⟩
    refine ⟨⟨sourceDomainParityProjection r a,sourceDomainParityProjection_mem r a⟩,Subtype.ext ?_⟩
    exact sourceDomainInclusion_parityProjection r a
  intro x
  exact closure_mono hr (hd x)

/-- Domain coefficients and their included parity-space vectors identify the exact operator domain. -/
def sourceParityUnboundedDomainEquiv (r : ℤ) : sourceDomainParitySubspace (p := p) r ≃ₗ[ℂ]
    LinearMap.range (sourceParityDomainInclusion (p := p) r).toLinearMap :=
  LinearEquiv.ofInjective (sourceParityDomainInclusion r).toLinearMap
    (sourceParityDomainInclusion_injective r)

@[simp] theorem sourceParityUnboundedDomainEquiv_coe (r : ℤ)
    (a : sourceDomainParitySubspace (p := p) r) :
    (sourceParityUnboundedDomainEquiv r a : sourceParitySubspace r) =
      sourceParityDomainInclusion r a := rfl

end NLS.ZakharovShabat
