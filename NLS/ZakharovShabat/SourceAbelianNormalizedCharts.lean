import NLS.ZakharovShabat.SourceAbelianHalfPlaneNormalization
import NLS.ZakharovShabat.SourceAbelianLocalExtension

/-! # Compatible zero-index abelian charts around every gap

Correcting a gap-normalized chart by `-i*n*pi` makes all charts agree
with the zero-index primitive on both half-planes. Continuity extends
this agreement to real overlap points as well. Every corrected chart
has the prescribed value `-i*n*pi` at its selected gap endpoints.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianDiscPrimitive
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p}
  {hφ : IsRealType (CoeffPair.toMax p φ)} {n m : ℤ}

/-- The selected chart with the common zero-index normalization. -/
def zeroNormalizedExtension (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) (z : ℂ) : ℂ :=
  D.extension z-I*(Real.pi : ℂ)*n

theorem zeroNormalizedExtension_hasDerivAt (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (z : ℂ) (hz : z ∈ D.extensionDomain) :
    HasDerivAt D.zeroNormalizedExtension
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z :=
  (D.extension_hasDerivAt z hz).sub_const (I*(Real.pi : ℂ)*n)

theorem zeroNormalizedExtension_analytic (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    AnalyticOnNhd ℂ D.zeroNormalizedExtension D.extensionDomain :=
  D.extension_analytic.sub analyticOnNhd_const

/-- The same zero-index half-plane function underlies every corrected chart. -/
theorem zeroNormalizedExtension_eq_halfPlane (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (upper : Bool) :
    EqOn D.zeroNormalizedExtension (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 upper)
      (sourceAbelianHalfPlane upper) := by
  intro z hz
  change D.extension z-I*(Real.pi : ℂ)*n = _
  rw [D.extension_eq_halfPlane upper hz,
    sourceAbelianHalfPlanePrimitive_eq_zeroIndex_add hp hp1 φ hφ n upper hz,add_sub_cancel_right]

/-- The corrected endpoint values agree with Lemma 19.1(ii), for all
approaches in the joined chart and for both open and collapsed gaps. -/
theorem zeroNormalizedExtension_endpoint_limit (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (a : ℂ) (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    Tendsto D.zeroNormalizedExtension (𝓝[D.extensionDomain] a) (𝓝 (-I*(Real.pi : ℂ)*n)) := by
  simpa only [zeroNormalizedExtension,zero_sub,neg_mul] using!
    (D.extension_endpoint_limit a ha).sub_const (I*(Real.pi : ℂ)*n)

/-- Charts normalized at different gaps, not just different charts of
the same gap, now agree everywhere on their common domain. -/
theorem zeroNormalizedExtension_eqOn_overlap
    (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (E : SourceAbelianDiscPrimitive hp hp1 φ hφ m) :
    EqOn D.zeroNormalizedExtension E.zeroNormalizedExtension (D.extensionDomain ∩ E.extensionDomain) := by
  intro z hz
  by_cases hu : 0 < z.im
  · exact (D.zeroNormalizedExtension_eq_halfPlane true hu).trans
      (E.zeroNormalizedExtension_eq_halfPlane true hu).symm
  by_cases hl : z.im < 0
  · exact (D.zeroNormalizedExtension_eq_halfPlane false hl).trans
      (E.zeroNormalizedExtension_eq_halfPlane false hl).symm
  have him : z.im = 0 := le_antisymm (le_of_not_gt hu) (le_of_not_gt hl)
  let := nhdsWithin_sourceAbelianHalfPlane_neBot true z him
  have hDlim : Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 true)
      (𝓝[sourceAbelianHalfPlane true] z) (𝓝 (D.zeroNormalizedExtension z)) := by
    apply ((D.zeroNormalizedExtension_hasDerivAt z hz.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact D.zeroNormalizedExtension_eq_halfPlane true hw
  have hElim : Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 true)
      (𝓝[sourceAbelianHalfPlane true] z) (𝓝 (E.zeroNormalizedExtension z)) := by
    apply ((E.zeroNormalizedExtension_hasDerivAt z hz.2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact E.zeroNormalizedExtension_eq_halfPlane true hw
  exact tendsto_nhds_unique hDlim hElim

end NLS.ZakharovShabat.SourceAbelianDiscPrimitive
