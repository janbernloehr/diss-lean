import NLS.ZakharovShabat.SourceParityUnboundedOperator
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Complete resolvent sets of the separate original Fourier parity operators -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Invertibility on a single parity is defined independently of the full periodic resolvent. -/
def sourceParityResolventSet (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) : Set ℂ :=
  {z | Function.Bijective (sourceParitySpectralPencil hp φ hφ r z)}

/-- The original full resolvent always restricts to either parity. -/
theorem mem_sourceParityResolventSet_of_full (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) (hz : z ∈ sourceResolventSet hp φ) :
    z ∈ sourceParityResolventSet hp φ hφ r :=
  ⟨Function.LeftInverse.injective (sourceParityResolvent_spectralPencil hp φ hφ r z hz),
    Function.RightInverse.surjective (sourceParitySpectralPencil_resolvent hp φ hφ r z hz)⟩

/-- The complete inverse in the original one-derivative norm exists at every sector resolvent point. -/
def sourceParityPencilEquiv (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceParityResolventSet hp φ hφ r) :
    sourceDomainParitySubspace (p := p) r ≃L[ℂ] sourceParitySubspace (p := p) r := by
  letI : CompleteSpace (sourceDomainParitySubspace (p := p) r) :=
    (isClosed_sourceDomainParitySubspace r).completeSpace_coe
  letI : CompleteSpace (sourceParitySubspace (p := p) r) :=
    (isClosed_sourceParitySubspace r).completeSpace_coe
  exact ContinuousLinearEquiv.ofBijective (sourceParitySpectralPencil hp φ hφ r z)
    (LinearMap.ker_eq_bot.mpr hz.1) (LinearMap.range_eq_top.mpr hz.2)

/-- The complete parity inverse, including parameters where the opposite sector has an eigenvalue. -/
def sourceParityFullResolventToDomain (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceParityResolventSet hp φ hφ r) :
    sourceParitySubspace (p := p) r →L[ℂ] sourceDomainParitySubspace (p := p) r :=
  (sourceParityPencilEquiv hp φ hφ r z hz).symm.toContinuousLinearMap

theorem sourceParityPencil_fullResolvent (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceParityResolventSet hp φ hφ r) (a : sourceParitySubspace (p := p) r) :
    sourceParitySpectralPencil hp φ hφ r z (sourceParityFullResolventToDomain hp φ hφ r z hz a) = a :=
  (sourceParityPencilEquiv hp φ hφ r z hz).apply_symm_apply a

theorem sourceParityFullResolvent_pencil (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceParityResolventSet hp φ hφ r) (a : sourceDomainParitySubspace (p := p) r) :
    sourceParityFullResolventToDomain hp φ hφ r z hz (sourceParitySpectralPencil hp φ hφ r z a) = a :=
  (sourceParityPencilEquiv hp φ hφ r z hz).symm_apply_apply a

/-- The full source domain is the sum of its two precise weighted parity domains. -/
theorem sourceDomainParityProjection_zero_add_one (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceDomainParityProjection 0 a + sourceDomainParityProjection 1 a = a := by
  apply sourceDomainInclusion_injective
  rw [map_add,sourceDomainInclusion_parityProjection,sourceDomainInclusion_parityProjection,
    sourceParityProjection_zero_add_one]

theorem sourceSpectralPencil_parityProjection (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceSpectralPencil hp φ z (sourceDomainParityProjection r a) =
      sourceParityProjection r (sourceSpectralPencil hp φ z a) := by
  simp only [sourceSpectralPencil_eq,sub_apply,smul_apply,
    sourceDomainInclusion_parityProjection,sourceOperator_domainParityProjection hp φ hφ,map_sub,map_smul]

/-- The full period-two pencil is invertible exactly when both separate parity pencils are invertible. -/
theorem mem_sourceResolventSet_iff_parity (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (z : ℂ) :
    z ∈ sourceResolventSet hp φ ↔
      z ∈ sourceParityResolventSet hp φ hφ 0 ∧ z ∈ sourceParityResolventSet hp φ hφ 1 := by
  constructor
  · intro hz
    exact ⟨mem_sourceParityResolventSet_of_full hp φ hφ 0 z hz,
      mem_sourceParityResolventSet_of_full hp φ hφ 1 z hz⟩
  · rintro ⟨h₀,h₁⟩
    have he (r : ℤ) (hr : z ∈ sourceParityResolventSet hp φ hφ r)
        (a b : WeightedCoeffPair (Weight.sobolev 1) p) (hab : sourceSpectralPencil hp φ z a = sourceSpectralPencil hp φ z b) :
        sourceDomainParityProjection r a = sourceDomainParityProjection r b := by
      have h : sourceParitySpectralPencil hp φ hφ r z
          ⟨sourceDomainParityProjection r a,sourceDomainParityProjection_mem r a⟩ =
          sourceParitySpectralPencil hp φ hφ r z
          ⟨sourceDomainParityProjection r b,sourceDomainParityProjection_mem r b⟩ := by
        apply Subtype.ext
        rw [sourceParitySpectralPencil_coe,sourceParitySpectralPencil_coe,
          sourceSpectralPencil_parityProjection hp φ hφ,sourceSpectralPencil_parityProjection hp φ hφ,hab]
      exact congrArg Subtype.val (hr.1 h)
    constructor
    · intro a b hab
      calc
        a = sourceDomainParityProjection 0 a + sourceDomainParityProjection 1 a :=
          (sourceDomainParityProjection_zero_add_one a).symm
        _ = sourceDomainParityProjection 0 b + sourceDomainParityProjection 1 b :=
          congrArg₂ (· + ·) (he 0 h₀ a b hab) (he 1 h₁ a b hab)
        _ = b := sourceDomainParityProjection_zero_add_one b
    · intro a
      obtain ⟨b,hb⟩ := h₀.2 ⟨sourceParityProjection 0 a,sourceParityProjection_mem 0 a⟩
      obtain ⟨c,hc⟩ := h₁.2 ⟨sourceParityProjection 1 a,sourceParityProjection_mem 1 a⟩
      refine ⟨b.val+c.val,?_⟩
      have hb' := congrArg Subtype.val hb
      have hc' := congrArg Subtype.val hc
      rw [sourceParitySpectralPencil_coe] at hb' hc'
      rw [map_add,hb',hc',sourceParityProjection_zero_add_one]

/-- Each actual parity spectrum is defined by failure of its own pencil to be invertible. -/
def sourceParitySpectrum (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) : Set ℂ :=
  (sourceParityResolventSet hp φ hφ r)ᶜ

/-- The original period-two spectrum is exactly the union of the two independently defined parity spectra. -/
theorem sourceSpectrum_eq_parity_union (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) :
    (sourceResolventSet hp φ)ᶜ = sourceParitySpectrum hp φ hφ 0 ∪ sourceParitySpectrum hp φ hφ 1 := by
  ext z
  change ¬ z ∈ sourceResolventSet hp φ ↔
    (¬ z ∈ sourceParityResolventSet hp φ hφ 0) ∨ (¬ z ∈ sourceParityResolventSet hp φ hφ 1)
  rw [mem_sourceResolventSet_iff_parity hp φ hφ z,not_and_or]

end NLS.ZakharovShabat
