import NLS.ComplexAnalysis.ContinuousBoundaryTransfer
import NLS.ZakharovShabat.SourceRealBandArcsin
import NLS.ZakharovShabat.SourceAbelianHalfPlane

/-! # Transfer the real-band increment to half-plane boundary values

An actual half-plane primitive continues across the whole vertical band
strip. Its boundary limits transfer to the real interval by continuity,
where the arcsine primitive fixes the increment as `-i*pi`.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The vertical strip above and below a real spectral band. -/
def sourceRealBandStrip (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : Set ℂ :=
  {z | z.re ∈ sourceRealBand hp hp1 φ n}

theorem isOpen_sourceRealBandStrip (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) :
    IsOpen (sourceRealBandStrip hp hp1 φ n) := isOpen_Ioo.preimage continuous_re

theorem convex_sourceRealBandStrip (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) :
    Convex ℝ (sourceRealBandStrip hp hp1 φ n) := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.re) := ⟨by simp,by simp⟩
  exact (convex_halfSpace_gt hlin _).inter (convex_halfSpace_lt hlin _)

/-- The full vertical strip avoids all cuts, including on the real axis. -/
theorem sourceRealBandStrip_subset_rootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    sourceRealBandStrip hp hp1 φ n ⊆ sourceCanonicalRootDomain hp hp1 φ := by
  intro z hz
  by_cases hi : z.im = 0
  · have he : z = (z.re : ℂ) := Complex.ext rfl hi
    rw [he]
    exact sourceRealBand_subset_rootDomain hp hp1 φ hφ n z.re hz
  · exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 φ hφ z hi

/-- A half-plane primitive extends to the band strip with exactly its
original values on the overlap, not just up to an unspecified constant. -/
theorem exists_sourceRealBandStrip_primitive_extension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool)
    (F : ℂ → ℂ) (hF : ∀ z ∈ sourceAbelianHalfPlane upper, HasDerivAt F
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z) :
    ∃ E : ℂ → ℂ,
      (∀ z ∈ sourceRealBandStrip hp hp1 φ n, HasDerivAt E
        (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z) ∧
      EqOn E F (sourceRealBandStrip hp hp1 φ n ∩ sourceAbelianHalfPlane upper) := by
  have hS := isOpen_sourceRealBandStrip hp hp1 φ n
  have hcS := convex_sourceRealBandStrip hp hp1 φ n
  obtain ⟨G,hG⟩ := exists_primitive_on_convex _ _ hcS hS
    ((sourceCriticalRootRatio_analyticOnNhd hp hp1 φ).mono
      (sourceRealBandStrip_subset_rootDomain hp hp1 φ hφ n)).differentiableOn
  obtain ⟨C,hC⟩ := (hS.inter (isOpen_sourceAbelianHalfPlane upper)).exists_eq_add_of_deriv_eq
    (hcS.inter (convex_sourceAbelianHalfPlane upper)).isPreconnected
    (fun z hz => (hG z hz.1).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz.2).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG z hz.1).deriv.trans (hF z hz.2).deriv.symm)
  refine ⟨fun z => G z-C,fun z hz => (hG z hz).sub_const C,?_⟩
  intro z hz
  change G z-C = F z
  rw [hC hz,add_sub_cancel_right]

/-- The endpoint limits of every actual half-plane primitive differ by
`-i*pi` across consecutive gaps, above and below the real axis alike. -/
theorem sourceAbelianHalfPlane_boundary_increment
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool)
    (F : ℂ → ℂ) (hF : ∀ z ∈ sourceAbelianHalfPlane upper, HasDerivAt F
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z)
    (A B : ℂ)
    (hA : Tendsto F (𝓝[sourceAbelianHalfPlane upper]
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 A))
    (hB : Tendsto F (𝓝[sourceAbelianHalfPlane upper]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1))) (𝓝 B)) :
    B-A = -I*(Real.pi : ℂ) := by
  let a := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re
  let P := sourceRealBandArcsinPrimitive hp φ n
  obtain ⟨E,hE,hmatch⟩ := exists_sourceRealBandStrip_primitive_extension hp hp1 φ hφ n upper F hF
  have hS := isOpen_sourceRealBandStrip hp hp1 φ n
  have hEc : ContinuousOn E (sourceRealBandStrip hp hp1 φ n) := fun z hz =>
    (hE z hz).continuousAt.continuousWithinAt
  have hmap (t : ℝ) : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[sourceRealBand hp hp1 φ n] t)
      (𝓝[sourceRealBandStrip hp hp1 φ n ∩ closure (sourceAbelianHalfPlane upper)] (t : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact ⟨hx,mem_closure_iff_nhdsWithin_neBot.mpr
        (nhdsWithin_sourceAbelianHalfPlane_neBot upper (x : ℂ) (by simp))⟩
  have ha : (a : ℂ) = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n := by
    refine Complex.ext (by rfl) ?_
    exact (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).2.symm
  have hb : (b : ℂ) = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1) := by
    refine Complex.ext (by rfl) ?_
    exact (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) (n+1)).1.symm
  have hEa : Tendsto (fun x : ℝ => E (x : ℂ)) (𝓝[sourceRealBand hp hp1 φ n] a) (𝓝 A) :=
    (tendsto_continuous_extension_on_closure F E _ _ (a : ℂ) A hS hEc hmatch
      (by rwa [ha])).comp (hmap a)
  have hEb : Tendsto (fun x : ℝ => E (x : ℂ)) (𝓝[sourceRealBand hp hp1 φ n] b) (𝓝 B) :=
    (tendsto_continuous_extension_on_closure F E _ _ (b : ℂ) B hS hEc hmatch
      (by rwa [hb])).comp (hmap b)
  have hd (x : ℝ) (hx : x ∈ sourceRealBand hp hp1 φ n) :
      HasDerivAt (fun x : ℝ => E (x : ℂ)-P x) 0 x := by
    simpa only [P,Pi.sub_apply,sub_self] using! (hE (x : ℂ) hx).comp_ofReal.sub
      (hasDerivAt_sourceRealBandArcsinPrimitive hp hp1 φ hφ n x hx)
  obtain ⟨C,hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (show DifferentiableOn ℝ (fun x : ℝ => E (x : ℂ)-P x) (sourceRealBand hp hp1 φ n) from
      fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv)
  have hlim (t : ℝ) : Tendsto (fun x : ℝ => E (x : ℂ))
      (𝓝[sourceRealBand hp hp1 φ n] t) (𝓝 (P t+C)) := by
    have hc : Continuous (fun x => P x+C) :=
      (continuous_sourceRealBandArcsinPrimitive hp hp1 φ n).add continuous_const
    apply ((hc.continuousAt (x := t)).tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have he : E (x : ℂ)-P x = C := hC x hx
    linear_combination -he
  have hab : a < b := canonicalPeriodicRight_re_lt_next_left hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  let : NeBot (𝓝[sourceRealBand hp hp1 φ n] a) := left_nhdsWithin_Ioo_neBot hab
  let : NeBot (𝓝[sourceRealBand hp hp1 φ n] b) := right_nhdsWithin_Ioo_neBot hab
  rw [tendsto_nhds_unique hEa (hlim a),tendsto_nhds_unique hEb (hlim b)]
  have hPa : P a = I*(Real.pi : ℂ)/2 := sourceRealBandArcsinPrimitive_left hp hp1 φ hφ n
  have hPb : P b = -I*(Real.pi : ℂ)/2 := sourceRealBandArcsinPrimitive_right hp hp1 φ hφ n
  rw [hPa,hPb]
  ring

end NLS.ZakharovShabat
