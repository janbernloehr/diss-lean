import NLS.ZakharovShabat.SourceAbelianPrimitiveExponent
import NLS.ZakharovShabat.SourcePsiGapRootIsospectral

/-! # Isospectral invariance of the endpoint-normalized primitives

Half-plane equality fixes the additive constant. Continuity gives the
same values on real bands, so arbitrary full spectral charts agree on
the complete canonical root domain of isospectral real sources.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized global primitive agrees throughout the common root domain. -/
theorem sourceAbelianGlobalPrimitive_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ) :
    EqOn (sourceAbelianGlobalPrimitive hp hp1 ψ.val ψ.property)
      (sourceAbelianGlobalPrimitive hp hp1 φ.val φ.property)
      (sourceCanonicalRootDomain hp hp1 ψ.val) := by
  have hhalf (upper : Bool) (z : ℂ) (hz : z ∈ sourceAbelianHalfPlane upper) :
      sourceAbelianGlobalPrimitive hp hp1 ψ.val ψ.property z =
        sourceAbelianGlobalPrimitive hp hp1 φ.val φ.property z := by
    rw [sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 ψ.val ψ.property upper hz,
      sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ.val φ.property upper hz]
    exact sourceAbelianHalfPlanePrimitive_eq_of_isospectral hp hp1 φ ψ h 0 upper hz
  intro z hz
  by_cases hu : 0 < z.im
  · exact hhalf true z hu
  by_cases hl : z.im < 0
  · exact hhalf false z hl
  have hreal : z.im = 0 := le_antisymm (not_lt.mp hu) (not_lt.mp hl)
  have hzφ : z ∈ sourceCanonicalRootDomain hp hp1 φ.val := by
    rwa [sourceCanonicalRootDomain_eq_of_isospectral hp hp1 φ ψ h] at hz
  apply eq_at_real_of_upperHalfPlane_extension _ _
    (sourceAbelianGlobalPrimitive hp hp1 ψ.val ψ.property)
    (sourceCanonicalRootDomain hp hp1 ψ.val) (sourceCanonicalRootDomain hp hp1 φ.val)
    z hreal
    (isOpen_sourceCanonicalRootDomain_of_realType hp hp1 ψ.val ψ.property)
    (isOpen_sourceCanonicalRootDomain_of_realType hp hp1 φ.val φ.property) hz hzφ
    (sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 ψ.val ψ.property z hz).continuousAt
    (sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 φ.val φ.property z hzφ).continuousAt
    (fun _ _ => rfl) (fun w hw => (hhalf true w hw.2).symm)

/-- Endpoint filling preserves equality off the spectral cuts. -/
theorem sourceAbelianPrimitive_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ.val) :
    sourceAbelianPrimitive hp hp1 ψ.val ψ.property z =
      sourceAbelianPrimitive hp hp1 φ.val φ.property z := by
  have hzφ := hz
  rw [sourceCanonicalRootDomain_eq_of_isospectral hp hp1 φ ψ h] at hzφ
  exact (sourceAbelianPrimitive_eq_global hp hp1 ψ.val ψ.property hz).trans
    ((sourceAbelianGlobalPrimitive_eq_of_isospectral hp hp1 φ ψ h hz).trans
      (sourceAbelianPrimitive_eq_global hp hp1 φ.val φ.property hzφ).symm)

/-- Arbitrary compatible full charts preserve the same indexed normalization. -/
theorem sourceFullAbelianPrimitive_real_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W V : Set (CoeffPair p))
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (D : SourceAbelianSpectralChart hp hp1 W ψ.val)
    (E : SourceAbelianSpectralChart hp hp1 V φ.val)
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ.val) :
    sourceFullAbelianPrimitive hp hp1 W n (z,ψ.val) =
      sourceFullAbelianPrimitive hp hp1 V n (z,φ.val) := by
  have hzφ := hz
  rw [sourceCanonicalRootDomain_eq_of_isospectral hp hp1 φ ψ h] at hzφ
  exact (sourceFullAbelianPrimitive_eq_real ψ D n z
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ.val hz)).trans
    ((congrArg (fun v : ℂ => v+I*(Real.pi:ℂ)*n)
      (sourceAbelianPrimitive_eq_of_isospectral hp hp1 φ ψ h z hz)).trans
      (sourceFullAbelianPrimitive_eq_real φ E n z
        (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val hzφ)).symm)

end NLS.ZakharovShabat
