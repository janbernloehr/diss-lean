import NLS.ZakharovShabat.SourceAbelianNormalizedCharts

/-! # Join both half-plane primitives across every real spectral band

A strip primitive fixed on the upper half-plane also matches the lower
half-plane. A corrected isolating-disc chart near the band's left end
provides the common real value that fixes the lower constant.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every band strip has a primitive compatible with the zero-index
normalization on both half-planes simultaneously. -/
theorem exists_sourceRealBandStrip_zeroNormalized_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ∃ E : ℂ → ℂ,
      (∀ z ∈ sourceRealBandStrip hp hp1 φ n, HasDerivAt E
        (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z) ∧
      ∀ upper : Bool, EqOn E (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 upper)
        (sourceRealBandStrip hp hp1 φ n ∩ sourceAbelianHalfPlane upper) := by
  obtain ⟨E,hE,hupper⟩ := exists_sourceRealBandStrip_primitive_extension hp hp1 φ hφ n true
    (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 true)
    (sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ 0 true).1
  obtain ⟨D⟩ := nonempty_sourceAbelianDiscPrimitive hp hp1 φ hφ n
  let a := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re
  have hab : a < b := canonicalPeriodicRight_re_lt_next_left hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  have ha : (a : ℂ) = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n := by
    refine Complex.ext (by rfl) ?_
    exact (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).2.symm
  have haball : (a : ℂ) ∈ ball D.center D.radius := by
    rw [ha]
    exact D.segment_subset (right_mem_segment ℝ _ _)
  let : NeBot (𝓝[sourceRealBand hp hp1 φ n] a) := left_nhdsWithin_Ioo_neBot hab
  have hnear : ∀ᶠ x : ℝ in 𝓝[sourceRealBand hp hp1 φ n] a, (x : ℂ) ∈ ball D.center D.radius :=
    (continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
      (isOpen_ball.mem_nhds haball)
  obtain ⟨x,hxball,hx⟩ := (hnear.and self_mem_nhdsWithin).exists
  have hxD : (x : ℂ) ∈ D.extensionDomain := Or.inr ⟨hxball,
    (sourceRealBand_subset_rootDomain hp hp1 φ hφ n x hx) n⟩
  have hS := isOpen_sourceRealBandStrip hp hp1 φ n
  have hne (upper : Bool) : NeBot
      (𝓝[sourceRealBandStrip hp hp1 φ n ∩ sourceAbelianHalfPlane upper] (x : ℂ)) := by
    rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (hS.mem_nhds hx))]
    exact nhdsWithin_sourceAbelianHalfPlane_neBot upper (x : ℂ) (by simp)
  have hDlim (upper : Bool) : Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 upper)
      (𝓝[sourceRealBandStrip hp hp1 φ n ∩ sourceAbelianHalfPlane upper] (x : ℂ))
      (𝓝 (D.zeroNormalizedExtension x)) := by
    apply ((D.zeroNormalizedExtension_hasDerivAt (x : ℂ) hxD).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact D.zeroNormalizedExtension_eq_halfPlane upper hz.2
  have hvalue : E x = D.zeroNormalizedExtension x := by
    let := hne true
    have he : Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 true)
        (𝓝[sourceRealBandStrip hp hp1 φ n ∩ sourceAbelianHalfPlane true] (x : ℂ)) (𝓝 (E x)) := by
      apply ((hE (x : ℂ) hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hupper hz
    exact tendsto_nhds_unique he (hDlim true)
  refine ⟨E,hE,?_⟩
  intro upper
  cases upper
  · let := hne false
    apply primitives_eq_of_common_boundary_limit _ _ _ _ (x : ℂ) (E x)
      (hS.inter (isOpen_sourceAbelianHalfPlane false))
      ((convex_sourceRealBandStrip hp hp1 φ n).inter (convex_sourceAbelianHalfPlane false)).isPreconnected
      (fun z hz => hE z hz.1)
      (fun z hz => (sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ 0 false).1 z hz.2)
      ((hE (x : ℂ) hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    rw [hvalue]
    exact hDlim false
  · exact hupper

end NLS.ZakharovShabat
