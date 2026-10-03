import NLS.ZakharovShabat.SourceAbelianGlobalProperties
import NLS.ZakharovShabat.SourceCollapsedGapNeighborhood
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # The real-source abelian primitive with collapsed gaps filled

The limit of the global cut-complement primitive supplies its missing
values. Riemann's removable singularity theorem proves analyticity at
collapsed endpoints. Only the noncollapsed cuts remain excluded.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original cut complement approaches every spectral point,
since it contains both open half-planes. -/
theorem nhdsWithin_sourceCanonicalRootDomain_neBot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ) :
    NeBot (𝓝[sourceCanonicalRootDomain hp hp1 φ] z) := by
  by_cases hi : z.im = 0
  · let := nhdsWithin_sourceAbelianHalfPlane_neBot true z hi
    exact Filter.neBot_of_le (nhdsWithin_mono z
      (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ true))
  · exact nhdsWithin_neBot_of_mem (sourceCanonicalRootDomain_of_im_ne_zero hp hp1 φ hφ z hi)

/-- The abelian primitive with the endpoint limits inserted. Its analytic
domain is the complement of the noncollapsed cuts. -/
def sourceAbelianPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ) : ℂ :=
  limUnder (𝓝[sourceCanonicalRootDomain hp hp1 φ] z) (sourceAbelianGlobalPrimitive hp hp1 φ hφ)

/-- Filling missing points preserves the original primitive everywhere
off the cuts. -/
theorem sourceAbelianPrimitive_eq_global
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    EqOn (sourceAbelianPrimitive hp hp1 φ hφ) (sourceAbelianGlobalPrimitive hp hp1 φ hφ)
      (sourceCanonicalRootDomain hp hp1 φ) := by
  intro z hz
  let := nhdsWithin_sourceCanonicalRootDomain_neBot hp hp1 φ hφ z
  simpa only [sourceAbelianPrimitive] using!
    ((sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 φ hφ z hz).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).limUnder_eq

/-- The inserted value is exactly the signed-index endpoint constant,
for either endpoint and also when the gap is collapsed. -/
theorem sourceAbelianPrimitive_periodicEndpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    sourceAbelianPrimitive hp hp1 φ hφ a = -I*(Real.pi : ℂ)*n := by
  let := nhdsWithin_sourceCanonicalRootDomain_neBot hp hp1 φ hφ a
  simpa only [sourceAbelianPrimitive] using!
    (sourceAbelianGlobalPrimitive_endpoint_limit hp hp1 φ hφ n a ha).limUnder_eq

/-- The original analytic germ is unchanged away from the cuts. -/
theorem sourceAbelianPrimitive_analyticAt_of_mem_rootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    AnalyticAt ℂ (sourceAbelianPrimitive hp hp1 φ hφ) z := by
  apply (sourceAbelianGlobalPrimitive_analytic hp hp1 φ hφ z hz).congr
  filter_upwards [(isOpen_sourceCanonicalRootDomain_of_realType hp hp1 φ hφ).mem_nhds hz] with w hw
  exact (sourceAbelianPrimitive_eq_global hp hp1 φ hφ hw).symm

/-- The finite endpoint limit removes the apparent singularity at every
collapsed gap, with no finite-gap or open-neighboring-gap assumption. -/
theorem sourceAbelianPrimitive_analyticAt_collapsed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    AnalyticAt ℂ (sourceAbelianPrimitive hp hp1 φ hφ)
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  obtain ⟨U,hU,ha,_,hsub⟩ := exists_sourceCollapsedGap_neighborhood hp hp1 φ hφ n hn
  have hlim : Tendsto (sourceAbelianGlobalPrimitive hp hp1 φ hφ) (𝓝[≠] a)
      (𝓝 (-I*(Real.pi : ℂ)*n)) := by
    rw [← nhdsWithin_sourceCanonicalRootDomain_collapsed hp hp1 φ hφ n hn]
    exact sourceAbelianGlobalPrimitive_endpoint_limit hp hp1 φ hφ n a (by simp [a])
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (hU.mem_nhds ha)] with z hza hzU
    exact (sourceAbelianPrimitive_analyticAt_of_mem_rootDomain hp hp1 φ hφ z
      (hsub ⟨hzU,hza⟩)).differentiableAt
  · rw [← continuousWithinAt_compl_self]
    change Tendsto (sourceAbelianPrimitive hp hp1 φ hφ) (𝓝[≠] a)
      (𝓝 (sourceAbelianPrimitive hp hp1 φ hφ a))
    rw [sourceAbelianPrimitive_periodicEndpoint hp hp1 φ hφ n a (by simp [a])]
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (hU.mem_nhds ha)] with z hza hzU
    exact (sourceAbelianPrimitive_eq_global hp hp1 φ hφ (hsub ⟨hzU,hza⟩)).symm

/-- The global real-source primitive is analytic on the plane with only
noncollapsed cuts removed. -/
theorem sourceAbelianPrimitive_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticOnNhd ℂ (sourceAbelianPrimitive hp hp1 φ hφ) (sourceOpenGapComplement hp hp1 φ) := by
  intro z hz
  rcases mem_sourceOpenGapComplement_cases hp hp1 φ z hz with hroot | ⟨n,hn,hseg⟩
  · exact sourceAbelianPrimitive_analyticAt_of_mem_rootDomain hp hp1 φ hφ z hroot
  · rw [sourcePeriodicSegment_eq_singleton_of_zeroGap hp hp1 φ n hn] at hseg
    rcases hseg with rfl
    exact sourceAbelianPrimitive_analyticAt_collapsed hp hp1 φ hφ n hn

end NLS.ZakharovShabat
