import NLS.ZakharovShabat.SourceAbelianBandSourceContinuity
import NLS.ZakharovShabat.SourceRootDomainConnected
import NLS.ComplexAnalysis.ParameterContinuityPropagation

/-! # Parameter continuity of the actual abelian primitive off all cuts

Nearby spectral increments equal increments of a joint analytic
logarithm chart: the unknown additive constants cancel. Continuity at
a real band anchor therefore propagates through the connected cut
complement, with the actual endpoint normalization retained.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near any spectral point off the cuts, differences of actual
primitive values vary continuously with the real source. -/
theorem eventually_continuousAt_sourceAbelianPrimitive_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (a : ℂ)
    (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    ∀ᶠ z : ℂ in 𝓝 a, ContinuousAt (fun ψ : realTypeSourceSubmodule p =>
      sourceAbelianPrimitive hp hp1 ψ.val ψ.property z-
        sourceAbelianPrimitive hp hp1 ψ.val ψ.property a) φ := by
  obtain ⟨V,hV,hbase,hroot,hcharts⟩ := exists_sourceAbelianLogChart_joint_neighborhood hp hp1 φ.val φ.property a ha
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hbase)
  have hsub : Metric.ball a r ×ˢ Metric.ball φ.val r ⊆ V := by
    rwa [ball_prod_same]
  have haB : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  have hφB : φ.val ∈ Metric.ball φ.val r := Metric.mem_ball_self hr
  let C := sourceAbelianLogChart hp hp1 φ.val φ.property a 0
  have hc (z : ℂ) (hz : z ∈ Metric.ball a r) :
      ContinuousAt (fun ψ : realTypeSourceSubmodule p => C (z,ψ.val)) φ := by
    have hm : Continuous (fun ψ : realTypeSourceSubmodule p => (z,ψ.val)) :=
      continuous_const.prodMk continuous_subtype_val
    simpa only [Function.comp_def] using!
      (((hcharts 0).1 (z,φ.val) (hsub ⟨hz,hφB⟩)).continuousAt.comp
        (f := fun ψ : realTypeSourceSubmodule p => (z,ψ.val)) (hm.continuousAt (x := φ)))
  filter_upwards [Metric.ball_mem_nhds a hr] with z hz
  apply ((hc z hz).sub (hc a haB)).congr_of_eventuallyEq
  have hnear : ∀ᶠ ψ : realTypeSourceSubmodule p in 𝓝 φ, ψ.val ∈ Metric.ball φ.val r :=
    (continuous_subtype_val.continuousAt (x := φ)).tendsto.eventually (Metric.ball_mem_nhds φ.val hr)
  filter_upwards [hnear] with ψ hψ
  have hd (w : ℂ) (hw : w ∈ Metric.ball a r) : DifferentiableAt ℂ (fun w => C (w,ψ.val)) w := by
    have hj := ((hcharts 0).1 (w,ψ.val) (hsub ⟨hw,hψ⟩)).differentiableAt
    simpa only [Function.comp_def] using! hj.comp w (differentiableAt_id.prodMk (differentiableAt_const ψ.val))
  have hF (w : ℂ) (hw : w ∈ Metric.ball a r) := sourceAbelianPrimitive_hasDerivAt_quotient hp hp1 ψ.val ψ.property w
    (hroot (w,ψ.val) (hsub ⟨hw,hψ⟩))
  obtain ⟨k,hk⟩ := Metric.isOpen_ball.exists_eq_add_of_deriv_eq (convex_ball a r).isPreconnected
    (show DifferentiableOn ℂ (fun w => C (w,ψ.val)) (Metric.ball a r) from
      fun w hw => (hd w hw).differentiableWithinAt)
    (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (sourceAbelianLogChart_spectral_deriv hp hp1 φ.val φ.property a 0 w ψ.val
      (by simpa only using! (hcharts 0).2 (w,ψ.val) (hsub ⟨hw,hψ⟩))).trans (hF w hw).deriv.symm)
  have hzEq := hk hz
  have haEq := hk haB
  change sourceAbelianPrimitive hp hp1 ψ.val ψ.property z-sourceAbelianPrimitive hp hp1 ψ.val ψ.property a = C (z,ψ.val)-C (a,ψ.val)
  linear_combination haEq-hzEq

/-- At every spectral point off the cuts, the actual normalized
primitive is continuous as the real potential varies. -/
theorem continuousAt_sourceAbelianPrimitive_source
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (a : ℂ)
    (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    ContinuousAt (fun ψ : realTypeSourceSubmodule p => sourceAbelianPrimitive hp hp1 ψ.val ψ.property a) φ := by
  obtain ⟨x,hx⟩ := exists_between (canonicalPeriodicRight_re_lt_next_left hp hp1
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) 0)
  have hxB : x ∈ sourceRealBand hp hp1 φ.val 0 := hx
  have hanchor : ContinuousAt (fun ψ : realTypeSourceSubmodule p =>
      sourceAbelianPrimitive hp hp1 ψ.val ψ.property (x : ℂ)) φ := by
    have hm : Continuous (fun ψ : realTypeSourceSubmodule p => (x,ψ)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using!
      ((continuousAt_sourceAbelianPrimitive_real_band hp hp1 φ 0 x hxB).comp
        (f := fun ψ : realTypeSourceSubmodule p => (x,ψ)) (hm.continuousAt (x := φ)))
  exact continuousAt_parameter_of_local_differences
    (fun z (ψ : realTypeSourceSubmodule p) => sourceAbelianPrimitive hp hp1 ψ.val ψ.property z)
    (sourceCanonicalRootDomain hp hp1 φ.val) φ
    (isConnected_sourceCanonicalRootDomain_of_realType hp hp1 φ.val φ.property).isPreconnected
    (fun z hz => (eventually_continuousAt_sourceAbelianPrimitive_sub hp hp1 φ z hz).filter_mono nhdsWithin_le_nhds)
    (x : ℂ) (sourceRealBand_subset_rootDomain hp hp1 φ.val φ.property 0 x hxB) hanchor a ha

end NLS.ZakharovShabat
