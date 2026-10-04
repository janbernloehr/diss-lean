import NLS.ZakharovShabat.SourceFullAbelianPrimitive
import NLS.ZakharovShabat.SourceAbelianHalfPlaneProperties
import NLS.ZakharovShabat.SourceCanonicalRootExponent

/-! # Exponent compatibility of normalized real-source primitives

The half-plane primitives already have the same endpoint normalization.
Continuity identifies their real-band values, so the full primitives
agree on the entire canonical root domain, with no additive constant.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourceAbelianGlobalPrimitive_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p) :
    EqOn (sourceAbelianGlobalPrimitive hp hp1 φ.val φ.property)
      (sourceAbelianGlobalPrimitive hq hq1 (CoeffPair.exponentInclusion hpq φ.val)
        (realTypeSourceExponentInclusion hpq φ).property)
      (sourceCanonicalRootDomain hp hp1 φ.val) := by
  let ψ := realTypeSourceExponentInclusion hpq φ
  have hhalf (upper : Bool) (z : ℂ) (hz : z ∈ sourceAbelianHalfPlane upper) :
      sourceAbelianGlobalPrimitive hp hp1 φ.val φ.property z =
        sourceAbelianGlobalPrimitive hq hq1 ψ.val ψ.property z := by
    rw [sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ.val φ.property upper hz,
      sourceAbelianGlobalPrimitive_eq_halfPlane hq hq1 ψ.val ψ.property upper hz]
    exact sourceAbelianHalfPlanePrimitive_exponent hp hq hp1 hq1 hpq φ 0 upper hz
  intro z hz
  by_cases hu : 0 < z.im
  · exact hhalf true z hu
  by_cases hl : z.im < 0
  · exact hhalf false z hl
  have hreal : z.im = 0 := le_antisymm (not_lt.mp hu) (not_lt.mp hl)
  have hzq : z ∈ sourceCanonicalRootDomain hq hq1 ψ.val := by
    rwa [sourceCanonicalRootDomain_exponent hp hq hp1 hq1 hpq φ.val] at hz
  apply eq_at_real_of_upperHalfPlane_extension _ _
    (sourceAbelianGlobalPrimitive hp hp1 φ.val φ.property)
    (sourceCanonicalRootDomain hp hp1 φ.val) (sourceCanonicalRootDomain hq hq1 ψ.val)
    z hreal
    (isOpen_sourceCanonicalRootDomain_of_realType hp hp1 φ.val φ.property)
    (isOpen_sourceCanonicalRootDomain_of_realType hq hq1 ψ.val ψ.property) hz hzq
    (sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 φ.val φ.property z hz).continuousAt
    (sourceAbelianGlobalPrimitive_hasDerivAt hq hq1 ψ.val ψ.property z hzq).continuousAt
    (fun _ _ => rfl) (fun w hw => (hhalf true w hw.2).symm)

/-- Filling the endpoints does not affect exponent compatibility off
all cuts, which is the domain used by the moment contours. -/
theorem sourceAbelianPrimitive_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAbelianPrimitive hp hp1 φ.val φ.property z =
      sourceAbelianPrimitive hq hq1 (CoeffPair.exponentInclusion hpq φ.val)
        (realTypeSourceExponentInclusion hpq φ).property z := by
  have hzq := hz
  rw [sourceCanonicalRootDomain_exponent hp hq hp1 hq1 hpq φ.val] at hzq
  exact (sourceAbelianPrimitive_eq_global hp hp1 φ.val φ.property hz).trans
    ((sourceAbelianGlobalPrimitive_exponent hp hq hp1 hq1 hpq φ hz).trans
      (sourceAbelianPrimitive_eq_global hq hq1 _
        (realTypeSourceExponentInclusion hpq φ).property hzq).symm)

/-- Full normalized primitives from arbitrary spectral charts have the
same values on a real source after changing its sequence exponent. -/
theorem sourceFullAbelianPrimitive_real_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (W : Set (CoeffPair p)) (V : Set (CoeffPair q)) (φ : realTypeSourceSubmodule p)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val)
    (E : SourceAbelianSpectralChart hq hq1 V (CoeffPair.exponentInclusion hpq φ.val))
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceFullAbelianPrimitive hp hp1 W n (z,φ.val) =
      sourceFullAbelianPrimitive hq hq1 V n (z,CoeffPair.exponentInclusion hpq φ.val) := by
  have hzq := hz
  rw [sourceCanonicalRootDomain_exponent hp hq hp1 hq1 hpq φ.val] at hzq
  exact (sourceFullAbelianPrimitive_eq_real φ D n z
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val hz)).trans
    ((congrArg (fun v : ℂ => v+I*(Real.pi:ℂ)*n)
      (sourceAbelianPrimitive_exponent hp hq hp1 hq1 hpq φ z hz)).trans
      (sourceFullAbelianPrimitive_eq_real (realTypeSourceExponentInclusion hpq φ) E n z
        (sourceCanonicalRootDomain_subset_openGapComplement hq hq1 _ hzq)).symm)

end NLS.ZakharovShabat
