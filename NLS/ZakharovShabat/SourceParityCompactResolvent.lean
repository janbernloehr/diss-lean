import NLS.ZakharovShabat.SourceParityResolventSet
import NLS.FunctionalAnalysis.CompactScalarPerturbation

/-! # Compact inverses and exact eigenvalue characterization in each Fourier parity -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full sector inverse agrees with restriction whenever the ambient inverse exists. -/
theorem sourceParityFullResolventToDomain_eq_restriction (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) (hz : z ∈ sourceResolventSet hp φ) :
    sourceParityFullResolventToDomain hp φ hφ r z (mem_sourceParityResolventSet_of_full hp φ hφ r z hz) =
      sourceParityResolventToDomain hp φ hφ r z hz := by
  ext a : 1
  apply (mem_sourceParityResolventSet_of_full hp φ hφ r z hz).1
  rw [sourceParityPencil_fullResolvent,sourceParitySpectralPencil_resolvent]

/-- The bounded sector inverse on its original base space. -/
def sourceParityFullResolvent (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceParityResolventSet hp φ hφ r) :
    sourceParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r :=
  (sourceParityDomainInclusion r).comp (sourceParityFullResolventToDomain hp φ hφ r z hz)

theorem sourceParityFullResolvent_of_full_coe (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) (hz : z ∈ sourceResolventSet hp φ)
    (a : sourceParitySubspace (p := p) r) :
    (sourceParityFullResolvent hp φ hφ r z (mem_sourceParityResolventSet_of_full hp φ hφ r z hz) a : CoeffPair p) =
      sourceResolvent hp φ z a.val := by
  unfold sourceParityFullResolvent
  rw [sourceParityFullResolventToDomain_eq_restriction hp φ hφ r z hz,sourceResolvent_eq_inclusion_comp]
  rfl

private theorem compact_sourceParityFullResolvent_of_full (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) (hz : z ∈ sourceResolventSet hp φ) :
    IsCompactOperator (sourceParityFullResolvent hp φ hφ r z (mem_sourceParityResolventSet_of_full hp φ hφ r z hz)) := by
  let P := (sourceParityProjection (p := p) r).codRestrict (sourceParitySubspace r) (sourceParityProjection_mem r)
  have he : sourceParityFullResolvent hp φ hφ r z (mem_sourceParityResolventSet_of_full hp φ hφ r z hz) =
      P.comp ((sourceResolvent hp φ z).comp (sourceParitySubspace (p := p) r).subtypeL) := by
    ext a : 1
    apply Subtype.ext
    rw [sourceParityFullResolvent_of_full_coe hp φ hφ r z hz a]
    change sourceResolvent hp φ z a.val = sourceParityProjection r (sourceResolvent hp φ z a.val)
    have hc := DFunLike.congr_fun (sourceParityProjection_commute_resolvent hp φ hφ r z hz).eq a.val
    change sourceParityProjection r (sourceResolvent hp φ z a.val) =
      sourceResolvent hp φ z (sourceParityProjection r a.val) at hc
    rw [(sourceParityProjection_eq_self_iff r a.val).mpr a.property] at hc
    exact hc.symm
  rw [he]
  exact ((isCompactOperator_sourceResolvent hp φ z).comp_clm (sourceParitySubspace (p := p) r).subtypeL).clm_comp P

/-- Every sector resolvent is compact, even when the opposite sector is singular. -/
theorem isCompactOperator_sourceParityFullResolvent (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceParityResolventSet hp φ hφ r) :
    IsCompactOperator (sourceParityFullResolvent hp φ hφ r z hz) := by
  obtain ⟨w,hw⟩ := resolventSet_nonempty hp (CoeffPair.toMax p φ)
  have hw' : w ∈ sourceResolventSet hp φ := by rwa [sourceResolventSet_eq]
  let hr := mem_sourceParityResolventSet_of_full hp φ hφ r w hw'
  have he : sourceParityFullResolvent hp φ hφ r z hz =
      (sourceParityFullResolvent hp φ hφ r w hr).comp
        ((sourceParitySpectralPencil hp φ hφ r w).comp (sourceParityFullResolventToDomain hp φ hφ r z hz)) := by
    ext a : 1
    change sourceParityDomainInclusion r (sourceParityFullResolventToDomain hp φ hφ r z hz a) =
      sourceParityDomainInclusion r (sourceParityFullResolventToDomain hp φ hφ r w hr
        (sourceParitySpectralPencil hp φ hφ r w (sourceParityFullResolventToDomain hp φ hφ r z hz a)))
    rw [sourceParityFullResolvent_pencil]
  rw [he]
  exact (compact_sourceParityFullResolvent_of_full hp φ hφ r w hw').comp_clm _

/-- The sector pencil factorization uses its own complete inverse. -/
theorem sourceParityPencil_comp_fullResolvent (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (w z : ℂ)
    (hw : w ∈ sourceParityResolventSet hp φ hφ r) :
    (sourceParitySpectralPencil hp φ hφ r z).comp (sourceParityFullResolventToDomain hp φ hφ r w hw) =
      1 + (z-w) • sourceParityFullResolvent hp φ hφ r w hw := by
  ext a : 1
  have h := sourceParityPencil_fullResolvent hp φ hφ r w hw a
  change w • sourceParityDomainInclusion r (sourceParityFullResolventToDomain hp φ hφ r w hw a) -
    sourceParityOperator hp φ hφ r (sourceParityFullResolventToDomain hp φ hφ r w hw a) = a at h
  change z • sourceParityDomainInclusion r (sourceParityFullResolventToDomain hp φ hφ r w hw a) -
    sourceParityOperator hp φ hφ r (sourceParityFullResolventToDomain hp φ hφ r w hw a) =
    a + (z-w) • sourceParityDomainInclusion r (sourceParityFullResolventToDomain hp φ hφ r w hw a)
  conv_rhs => lhs; rw [← h]
  module

/-- Compactness rules out a continuous or residual spectrum in either sector. -/
theorem sourceParityPencil_bijective_of_injective (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hi : Function.Injective (sourceParitySpectralPencil hp φ hφ r z)) :
    Function.Bijective (sourceParitySpectralPencil hp φ hφ r z) := by
  let : CompleteSpace (sourceParitySubspace (p := p) r) :=
    (isClosed_sourceParitySubspace r).completeSpace_coe
  obtain ⟨w,hw⟩ := resolventSet_nonempty hp (CoeffPair.toMax p φ)
  have hw' : w ∈ sourceResolventSet hp φ := by rwa [sourceResolventSet_eq]
  let hr := mem_sourceParityResolventSet_of_full hp φ hφ r w hw'
  have hR : Function.Bijective (sourceParityFullResolventToDomain hp φ hφ r w hr) :=
    (sourceParityPencilEquiv hp φ hφ r w hr).symm.bijective
  let A := (sourceParitySpectralPencil hp φ hφ r z).comp (sourceParityFullResolventToDomain hp φ hφ r w hr)
  have hc : IsCompactOperator (A - (1 : ℂ) • (1 : sourceParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r)) := by
    dsimp only [A]
    rw [sourceParityPencil_comp_fullResolvent,one_smul,add_sub_cancel_left]
    exact (isCompactOperator_sourceParityFullResolvent hp φ hφ r w hr).smul (z-w)
  have hb := NLS.CompactScalarPerturbation.bijective_of_injective A one_ne_zero hc (hi.comp hR.1)
  exact (Function.Bijective.of_comp_iff _ hR).mp hb

/-- A sector spectral point is exactly a nonzero vector in its actual one-derivative kernel. -/
theorem mem_sourceParitySpectrum_iff_exists_kernel (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) :
    z ∈ sourceParitySpectrum hp φ hφ r ↔
      ∃ a : sourceDomainParitySubspace (p := p) r, a ≠ 0 ∧ sourceParitySpectralPencil hp φ hφ r z a = 0 := by
  constructor
  · intro hz
    by_contra hn
    apply hz
    apply sourceParityPencil_bijective_of_injective
    intro a b hab
    have hk : sourceParitySpectralPencil hp φ hφ r z (a-b) = 0 := by rw [map_sub,hab,sub_self]
    have he : a-b = 0 := by by_contra hne; exact hn ⟨a-b,hne,hk⟩
    exact sub_eq_zero.mp he
  · rintro ⟨a,hne,ha⟩ hz
    exact hne (hz.1 (ha.trans (map_zero _).symm))

end NLS.ZakharovShabat
