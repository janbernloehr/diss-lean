import NLS.ZakharovShabat.ParityIntervalL2Equiv
import NLS.ZakharovShabat.SourceParityOperatorDomain

/-! # Exact full classical domains inside the original unit-interval L² space -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

theorem HasClassicalParityDomain.memLp {r : ℤ} {f : ℝ → ℂ × ℂ}
    (hf : HasClassicalParityDomain r f) : MemLp f 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨memLp_of_intervalH1Regularity hf.fst_regular,memLp_of_intervalH1Regularity hf.snd_regular⟩

/-- Inclusion of the actual one-derivative parity domain into physical unit-interval L². -/
def unitParityDomainInclusion (r : ℤ) :
    sourceDomainParitySubspace (p := 2) r →L[ℂ] IntervalPairL2 :=
  (sourceParityUnitEquiv r).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sourceParityDomainInclusion r)

theorem unitParityDomainInclusion_injective (r : ℤ) :
    Function.Injective (unitParityDomainInclusion r) :=
  (sourceParityUnitEquiv r).injective.comp (sourceParityDomainInclusion_injective r)

theorem unitParityDomainInclusion_denseRange (r : ℤ) : DenseRange (unitParityDomainInclusion r) :=
  (sourceParityUnitEquiv r).surjective.denseRange.comp
    (sourceParityDomainInclusion_denseRange (by simp) r) (sourceParityUnitEquiv r).continuous

/-- Actual representatives are preserved by the full classical domain inclusion. -/
theorem unitParityDomainInclusion_representative (r : ℤ)
    (a : sourceDomainParitySubspace (p := 2) r) :
    intervalL2Representative (unitParityDomainInclusion r a) =ᵐ[volume.restrict (Ioc 0 1)]
      physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a.val) := by
  apply (sourceParityUnitEquiv_representative r (sourceParityDomainInclusion r a)).trans
  exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (physicalBase_domainInclusion _)

/-- Classical signed extension in the original component-sum weighted norm. -/
def sourceClassicalParityExtension (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalParityDomain r f) : sourceDomainParitySubspace (p := 2) r :=
  ⟨(WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalParityExtension r f hf), by
    change (WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalParityExtension r f hf)) ∈ domainParitySubspace r
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact classicalParityExtension_mem r f hf⟩

/-- The included signed extension is exactly the class of the original classical function. -/
theorem unitParityDomainInclusion_classicalExtension (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalParityDomain r f) :
    unitParityDomainInclusion r (sourceClassicalParityExtension r f hf) = intervalL2OfFunction f hf.memLp := by
  apply intervalL2Representative_injective
  have h := unitParityDomainInclusion_representative r (sourceClassicalParityExtension r f hf)
  change intervalL2Representative (unitParityDomainInclusion r (sourceClassicalParityExtension r f hf))
    =ᵐ[volume.restrict (Ioc 0 1)] physicalDomain ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalParityExtension r f hf))) at h
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  filter_upwards [h,intervalL2Representative_ofFunction f hf.memLp,
    ae_restrict_mem measurableSet_Ioc] with x hx hy hmem
  rw [hx,classicalParityExtension_restrict r f hf ⟨hmem.1.le,hmem.2⟩,hy]

/-- Domain membership is exactly existence of a full classical H¹ representative with the specified sign. -/
theorem mem_unitParityDomain_iff (r : ℤ) (u : IntervalPairL2) :
    u ∈ LinearMap.range (unitParityDomainInclusion r).toLinearMap ↔
      ∃ (f : ℝ → ℂ × ℂ) (hf : HasClassicalParityDomain r f), intervalL2OfFunction f hf.memLp = u := by
  constructor
  · rintro ⟨a,rfl⟩
    let f := physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a.val)
    let hf := physicalDomain_mem_classicalParityDomain r
      (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a.val) a.property
    refine ⟨f,hf,?_⟩
    exact intervalL2Representative_injective _ _
      ((intervalL2Representative_ofFunction f hf.memLp).trans (unitParityDomainInclusion_representative r a).symm)
  · rintro ⟨f,hf,rfl⟩
    exact ⟨sourceClassicalParityExtension r f hf,unitParityDomainInclusion_classicalExtension r f hf⟩

/-- Exact coefficients of the actual dense domain of the unit-interval operator. -/
def unitParityDomainEquiv (r : ℤ) : sourceDomainParitySubspace (p := 2) r ≃ₗ[ℂ]
    LinearMap.range (unitParityDomainInclusion r).toLinearMap :=
  LinearEquiv.ofInjective (unitParityDomainInclusion r).toLinearMap (unitParityDomainInclusion_injective r)

@[simp] theorem unitParityDomainEquiv_coe (r : ℤ) (a : sourceDomainParitySubspace (p := 2) r) :
    (unitParityDomainEquiv r a : IntervalPairL2) = sourceParityUnitEquiv r (sourceParityDomainInclusion r a) := rfl

end NLS.ZakharovShabat
