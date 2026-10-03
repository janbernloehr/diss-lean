import NLS.ZakharovShabat.SourceAbelianBandGluing
import NLS.ZakharovShabat.SourceRealBandCoverage

/-! # The global real-source abelian primitive off all spectral cuts

The upper and lower zero-index primitives and the compatible band-strip
primitives define one analytic function on the entire cut complement.
The gluing is independent of the chosen strip and primitive.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A compatible primitive on each full vertical band strip. -/
def sourceAbelianBandPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) : ℂ → ℂ :=
  (exists_sourceRealBandStrip_zeroNormalized_primitive hp hp1 φ hφ n).choose

theorem sourceAbelianBandPrimitive_spec
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (∀ z ∈ sourceRealBandStrip hp hp1 φ n, HasDerivAt (sourceAbelianBandPrimitive hp hp1 φ hφ n)
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z) ∧
    ∀ upper : Bool, EqOn (sourceAbelianBandPrimitive hp hp1 φ hφ n)
      (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 upper)
      (sourceRealBandStrip hp hp1 φ n ∩ sourceAbelianHalfPlane upper) :=
  (exists_sourceRealBandStrip_zeroNormalized_primitive hp hp1 φ hφ n).choose_spec

/-- Continuous local extensions of the same upper-half-plane function
have the same value at a real point of their open domains. -/
theorem eq_at_real_of_upperHalfPlane_extension
    (F G H : ℂ → ℂ) (U V : Set ℂ) (z : ℂ) (hz : z.im = 0)
    (hU : IsOpen U) (hV : IsOpen V) (hzU : z ∈ U) (hzV : z ∈ V)
    (hF : ContinuousAt F z) (hG : ContinuousAt G z)
    (hFU : EqOn F H (U ∩ sourceAbelianHalfPlane true))
    (hGV : EqOn G H (V ∩ sourceAbelianHalfPlane true)) : F z = G z := by
  let := nhdsWithin_sourceAbelianHalfPlane_neBot true z hz
  have hlim (E : ℂ → ℂ) (W : Set ℂ) (hW : IsOpen W) (hzW : z ∈ W)
      (hE : ContinuousAt E z) (hEW : EqOn E H (W ∩ sourceAbelianHalfPlane true)) :
      Tendsto H (𝓝[sourceAbelianHalfPlane true] z) (𝓝 (E z)) := by
    apply (hE.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (hW.mem_nhds hzW)] with w hw hwW
    exact hEW ⟨hwW,hw⟩
  exact tendsto_nhds_unique (hlim F U hU hzU hF hFU) (hlim G V hV hzV hG hGV)

/-- The global zero-index abelian primitive for real sources. Values
outside the cut complement are immaterial at this stage. -/
def sourceAbelianGlobalPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ) : ℂ := by
  classical
  exact if 0 < z.im then sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 true z
    else if z.im < 0 then sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 false z
    else if h : ∃ n : ℤ, z ∈ sourceRealBandStrip hp hp1 φ n then
      sourceAbelianBandPrimitive hp hp1 φ hφ h.choose z
    else 0

theorem sourceAbelianGlobalPrimitive_eq_halfPlane
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (upper : Bool) :
    EqOn (sourceAbelianGlobalPrimitive hp hp1 φ hφ)
      (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 upper) (sourceAbelianHalfPlane upper) := by
  intro z hz
  cases upper
  · have h : z.im < 0 := hz
    simp [sourceAbelianGlobalPrimitive,h,not_lt.mpr h.le]
  · have h : 0 < z.im := hz
    simp [sourceAbelianGlobalPrimitive,h]

/-- The global function matches each strip chart, so no choice of a
band index or of a primitive affects the continued values. -/
theorem sourceAbelianGlobalPrimitive_eq_band
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    EqOn (sourceAbelianGlobalPrimitive hp hp1 φ hφ)
      (sourceAbelianBandPrimitive hp hp1 φ hφ n) (sourceRealBandStrip hp hp1 φ n) := by
  intro z hz
  have hs := sourceAbelianBandPrimitive_spec hp hp1 φ hφ n
  by_cases hu : 0 < z.im
  · exact (sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ true hu).trans (hs.2 true ⟨hz,hu⟩).symm
  by_cases hl : z.im < 0
  · exact (sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ false hl).trans (hs.2 false ⟨hz,hl⟩).symm
  have h : ∃ m : ℤ, z ∈ sourceRealBandStrip hp hp1 φ m := ⟨n,hz⟩
  simp only [sourceAbelianGlobalPrimitive,hu,hl,ite_false,dif_pos h]
  have hm := sourceAbelianBandPrimitive_spec hp hp1 φ hφ h.choose
  exact eq_at_real_of_upperHalfPlane_extension _ _ _ _ _ z
    (le_antisymm (le_of_not_gt hu) (le_of_not_gt hl))
    (isOpen_sourceRealBandStrip hp hp1 φ h.choose) (isOpen_sourceRealBandStrip hp hp1 φ n)
    h.choose_spec hz (hm.1 z h.choose_spec).continuousAt (hs.1 z hz).continuousAt
    (hm.2 true) (hs.2 true)

/-- The actual spectral quotient is the derivative on the entire cut
complement, including every real band point. -/
theorem sourceAbelianGlobalPrimitive_hasDerivAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    HasDerivAt (sourceAbelianGlobalPrimitive hp hp1 φ hφ)
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z := by
  rw [sourceCanonicalRootDomain_eq_halfPlanes_union_bandStrips hp hp1 φ hφ] at hz
  rcases hz with (hu | hl) | hs
  · apply ((sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ 0 true).1 z hu).congr_of_eventuallyEq
    filter_upwards [(isOpen_sourceAbelianHalfPlane true).mem_nhds hu] with w hw
    exact sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ true hw
  · apply ((sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ 0 false).1 z hl).congr_of_eventuallyEq
    filter_upwards [(isOpen_sourceAbelianHalfPlane false).mem_nhds hl] with w hw
    exact sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ false hw
  · obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    apply ((sourceAbelianBandPrimitive_spec hp hp1 φ hφ n).1 z hn).congr_of_eventuallyEq
    filter_upwards [(isOpen_sourceRealBandStrip hp hp1 φ n).mem_nhds hn] with w hw
    exact sourceAbelianGlobalPrimitive_eq_band hp hp1 φ hφ n hw

theorem sourceAbelianGlobalPrimitive_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticOnNhd ℂ (sourceAbelianGlobalPrimitive hp hp1 φ hφ) (sourceCanonicalRootDomain hp hp1 φ) :=
  (show DifferentiableOn ℂ (sourceAbelianGlobalPrimitive hp hp1 φ hφ) (sourceCanonicalRootDomain hp hp1 φ)
    from fun z hz => (sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 φ hφ z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
    (isOpen_sourceCanonicalRootDomain_of_realType hp hp1 φ hφ)

/-- All corrected isolating-disc charts are restrictions of the same
global primitive, for every signed gap index. -/
theorem sourceAbelianGlobalPrimitive_eq_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    EqOn (sourceAbelianGlobalPrimitive hp hp1 φ hφ) D.zeroNormalizedExtension D.extensionDomain := by
  intro z hz
  by_cases hu : 0 < z.im
  · exact (sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ true hu).trans
      (D.zeroNormalizedExtension_eq_halfPlane true hu).symm
  by_cases hl : z.im < 0
  · exact (sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ false hl).trans
      (D.zeroNormalizedExtension_eq_halfPlane false hl).symm
  exact eq_at_real_of_upperHalfPlane_extension _ _ _ _ _ z
    (le_antisymm (le_of_not_gt hu) (le_of_not_gt hl))
    (isOpen_sourceCanonicalRootDomain_of_realType hp hp1 φ hφ) D.isOpen_extensionDomain
    (D.extensionDomain_subset_rootDomain hz) hz
    (sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 φ hφ z (D.extensionDomain_subset_rootDomain hz)).continuousAt
    (D.zeroNormalizedExtension_hasDerivAt z hz).continuousAt
    (fun _ hw => sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ true hw.2)
    (fun _ hw => D.zeroNormalizedExtension_eq_halfPlane true hw.2)

end NLS.ZakharovShabat
