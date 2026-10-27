import NLS.ZakharovShabat.SourceParityCompactResolvent
import NLS.ZakharovShabat.UnitParitySelfAdjoint

/-! # Actual bounded resolvents on the full classical unit-interval domains -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The physical pencil intertwines the actual full domain and base-space identifications. -/
theorem unitParityPencil_intertwining (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (a : sourceDomainParitySubspace (p := 2) r) :
    linearPMapPencil (unitParityOperator φ hφ r) z (unitParityDomainEquiv r a) =
      sourceParityUnitEquiv r (sourceParitySpectralPencil (by simp) φ hφ r z a) := by
  rw [linearPMapPencil_apply,unitParityDomainEquiv_coe,unitParityOperator_apply]
  change z • sourceParityUnitEquiv r (sourceParityDomainInclusion r a) -
    sourceParityUnitEquiv r (sourceParityOperator (by simp) φ hφ r a) =
    sourceParityUnitEquiv r (z • sourceParityDomainInclusion r a-sourceParityOperator (by simp) φ hφ r a)
  rw [map_sub,map_smul]

/-- Physical pencil bijectivity is equivalent to bijectivity in the original weighted parity domain. -/
theorem unitParityPencil_bijective_iff (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) :
    Function.Bijective (linearPMapPencil (unitParityOperator φ hφ r) z) ↔
      z ∈ sourceParityResolventSet (by simp) φ hφ r := by
  have he : linearPMapPencil (unitParityOperator φ hφ r) z ∘ unitParityDomainEquiv r =
      sourceParityUnitEquiv r ∘ sourceParitySpectralPencil (by simp) φ hφ r z :=
    funext (unitParityPencil_intertwining φ hφ r z)
  rw [← Function.Bijective.of_comp_iff _ (unitParityDomainEquiv r).bijective,he,
    Function.Bijective.of_comp_iff' (sourceParityUnitEquiv r).bijective]
  rfl

/-- Resolvent membership uses an actual bounded two-sided inverse on the physical partial-operator domain. -/
def unitParityResolventSet (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) : Set ℂ :=
  {z | ∃ R : IntervalPairL2 →L[ℂ] (unitParityOperator φ hφ r).domain,
    (∀ f, linearPMapPencil (unitParityOperator φ hφ r) z (R f) = f) ∧
    (∀ g, R (linearPMapPencil (unitParityOperator φ hφ r) z g) = g)}

/-- Inclusion into the actual partial-operator domain is continuous from the original weighted domain norm. -/
def unitParityDomainEmbedding (r : ℤ) : sourceDomainParitySubspace (p := 2) r →L[ℂ]
    LinearMap.range (unitParityDomainInclusion r).toLinearMap :=
  (unitParityDomainInclusion r).codRestrict _ (fun a => ⟨a,rfl⟩)

@[simp] theorem unitParityDomainEmbedding_apply (r : ℤ) (a : sourceDomainParitySubspace (p := 2) r) :
    unitParityDomainEmbedding r a = unitParityDomainEquiv r a := rfl

/-- The bounded inverse into the full classical physical domain at every sector resolvent parameter. -/
def unitParityFullResolventToDomain (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (hz : z ∈ sourceParityResolventSet (by simp) φ hφ r) :
    IntervalPairL2 →L[ℂ] (unitParityOperator φ hφ r).domain :=
  (unitParityDomainEmbedding r).comp ((sourceParityFullResolventToDomain (by simp) φ hφ r z hz).comp
    (sourceParityUnitEquiv r).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem unitParityPencil_fullResolvent (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (hz : z ∈ sourceParityResolventSet (by simp) φ hφ r) (f : IntervalPairL2) :
    linearPMapPencil (unitParityOperator φ hφ r) z (unitParityFullResolventToDomain φ hφ r z hz f) = f := by
  change linearPMapPencil (unitParityOperator φ hφ r) z (unitParityDomainEquiv r
    (sourceParityFullResolventToDomain (by simp) φ hφ r z hz ((sourceParityUnitEquiv r).symm f))) = f
  rw [unitParityPencil_intertwining,sourceParityPencil_fullResolvent,LinearIsometryEquiv.apply_symm_apply]

theorem unitParityFullResolvent_pencil (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (hz : z ∈ sourceParityResolventSet (by simp) φ hφ r)
    (f : (unitParityOperator φ hφ r).domain) :
    unitParityFullResolventToDomain φ hφ r z hz (linearPMapPencil (unitParityOperator φ hφ r) z f) = f := by
  obtain ⟨a,rfl⟩ := (unitParityDomainEquiv r).surjective f
  rw [unitParityPencil_intertwining]
  change unitParityDomainEquiv r (sourceParityFullResolventToDomain (by simp) φ hφ r z hz
    ((sourceParityUnitEquiv r).symm (sourceParityUnitEquiv r
      (sourceParitySpectralPencil (by simp) φ hφ r z a)))) = unitParityDomainEquiv r a
  rw [LinearIsometryEquiv.symm_apply_apply,sourceParityFullResolvent_pencil]

/-- Bounded invertibility on the actual physical domain has exactly the original sector parameters. -/
theorem mem_unitParityResolventSet_iff (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) :
    z ∈ unitParityResolventSet φ hφ r ↔ z ∈ sourceParityResolventSet (by simp) φ hφ r := by
  constructor
  · rintro ⟨R,h₁,h₂⟩
    exact (unitParityPencil_bijective_iff φ hφ r z).mp
      ⟨Function.LeftInverse.injective h₂,Function.RightInverse.surjective h₁⟩
  · intro hz
    exact ⟨unitParityFullResolventToDomain φ hφ r z hz,
      unitParityPencil_fullResolvent φ hφ r z hz,unitParityFullResolvent_pencil φ hφ r z hz⟩

/-- The actual bounded physical base-space resolvent. -/
def unitParityFullResolvent (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (hz : z ∈ sourceParityResolventSet (by simp) φ hφ r) :
    IntervalPairL2 →L[ℂ] IntervalPairL2 :=
  (unitParityOperator φ hφ r).domain.subtypeL.comp (unitParityFullResolventToDomain φ hφ r z hz)

/-- The actual base-space inverses are conjugate by physical restriction. -/
theorem unitParityFullResolvent_eq_conjugate (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (hz : z ∈ sourceParityResolventSet (by simp) φ hφ r) :
    unitParityFullResolvent φ hφ r z hz =
      (sourceParityUnitEquiv r).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((sourceParityFullResolvent (by simp) φ hφ r z hz).comp
          (sourceParityUnitEquiv r).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext f : 1
  rfl

/-- The actual physical resolvent is compact for arbitrary complex L² potentials. -/
theorem isCompactOperator_unitParityFullResolvent (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (hz : z ∈ sourceParityResolventSet (by simp) φ hφ r) :
    IsCompactOperator (unitParityFullResolvent φ hφ r z hz) := by
  rw [unitParityFullResolvent_eq_conjugate]
  exact ((isCompactOperator_sourceParityFullResolvent (by simp) φ hφ r z hz).comp_clm
    (sourceParityUnitEquiv r).symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    (sourceParityUnitEquiv r).toContinuousLinearEquiv.toContinuousLinearMap

/-- Physical spectrum means failure of bounded invertibility, independently of any eigenvalue list. -/
def unitParitySpectrum (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) : Set ℂ :=
  (unitParityResolventSet φ hφ r)ᶜ

theorem unitParitySpectrum_eq (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    unitParitySpectrum φ hφ r = sourceParitySpectrum (by simp) φ hφ r := by
  ext z
  exact not_congr (mem_unitParityResolventSet_iff φ hφ r z)

end NLS.ZakharovShabat
