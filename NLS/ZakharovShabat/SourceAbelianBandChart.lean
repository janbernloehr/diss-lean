import NLS.ZakharovShabat.SourceAbelianBandSourceContinuity

/-! # Actual abelian integral charts near a real spectral band

A product of spectral and complex-source balls supports all indexed
analytic logarithm charts. On every nearby real-source slice these
charts agree with the actual normalized abelian integral throughout
the complex spectral ball. Equality at the real band anchor propagates
by equality of spectral derivatives on that connected ball.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near a real band anchor, the joint analytic charts extend the
actual normalized primitive for every nearby real source. The same
product neighborhood works for all signed normalization indices. -/
theorem exists_sourceAbelianLogChart_band_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (m : ℤ) (a : ℝ)
    (ha : a ∈ sourceRealBand hp hp1 φ.val m) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t ∈ Metric.ball (a : ℂ) r ×ˢ Metric.ball φ.val r,
        t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2) ∧
      ∀ n : ℤ,
        AnalyticOnNhd ℂ (sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n)
          (Metric.ball (a : ℂ) r ×ˢ Metric.ball φ.val r) ∧
        (∀ t ∈ Metric.ball (a : ℂ) r ×ˢ Metric.ball φ.val r,
          HasFDerivAt (sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n)
            ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
              fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t) ∧
        ∀ (ψ : realTypeSourceSubmodule p), ψ.val ∈ Metric.ball φ.val r →
          ∀ z ∈ Metric.ball (a : ℂ) r,
            sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n (z,ψ.val) =
              sourceAbelianPrimitive hp hp1 ψ.val ψ.property z+I*(Real.pi : ℂ)*n := by
  obtain ⟨V,hV,hbase,hroot,hcharts⟩ := exists_sourceAbelianLogChart_joint_neighborhood
    hp hp1 φ.val φ.property (a : ℂ) (sourceRealBand_subset_rootDomain hp hp1 φ.val φ.property m a ha)
  obtain ⟨R,hR,hRV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hbase)
  have hm : Continuous (fun ψ : realTypeSourceSubmodule p => (a,ψ)) := continuous_const.prodMk continuous_id
  have he := (hm.continuousAt (x := φ)).tendsto.eventually
    (sourceAbelianLogChart_eventually_eq_nearby_real_sources hp hp1 φ m a ha)
  obtain ⟨δ,hδ,hδeq⟩ := Metric.mem_nhds_iff.mp he
  let r := min R δ
  have hr : 0 < r := lt_min hR hδ
  have hsub : Metric.ball (a : ℂ) r ×ˢ Metric.ball φ.val r ⊆ V := by
    rw [ball_prod_same]
    exact (Metric.ball_subset_ball (min_le_left R δ)).trans hRV
  refine ⟨r,hr,fun t ht => hroot t (hsub ht),?_⟩
  intro n
  refine ⟨(hcharts n).1.mono hsub,fun t ht => (hcharts n).2 t (hsub ht),?_⟩
  intro ψ hψ
  have hψδ : ψ ∈ Metric.ball φ δ :=
    lt_of_lt_of_le hψ (min_le_right R δ)
  have heq : sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n ((a : ℂ),ψ.val) =
      sourceAbelianPrimitive hp hp1 ψ.val ψ.property (a : ℂ)+I*(Real.pi : ℂ)*n := hδeq hψδ n
  have hd (z : ℂ) (hz : z ∈ Metric.ball (a : ℂ) r) :
      DifferentiableAt ℂ (fun w : ℂ => sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n (w,ψ.val)) z := by
    have hc := ((hcharts n).1 (z,ψ.val) (hsub ⟨hz,hψ⟩)).differentiableAt
    simpa only [Function.comp_def] using! hc.comp z (differentiableAt_id.prodMk (differentiableAt_const ψ.val))
  have hF (z : ℂ) (hz : z ∈ Metric.ball (a : ℂ) r) :=
    (sourceAbelianPrimitive_hasDerivAt_quotient hp hp1 ψ.val ψ.property z
      (hroot (z,ψ.val) (hsub ⟨hz,hψ⟩))).add_const (I*(Real.pi : ℂ)*n)
  apply Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (a : ℂ) r).isPreconnected
    (fun z hz => (hd z hz).differentiableWithinAt)
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => ?_) (Metric.mem_ball_self hr) heq
  rw [(hF z hz).deriv]
  exact sourceAbelianLogChart_spectral_deriv hp hp1 φ.val φ.property (a : ℂ) n z ψ.val
    (by simpa only using! (hcharts n).2 (z,ψ.val) (hsub ⟨hz,hψ⟩))

/-- The actual primitive is jointly continuous in complex spectral
coordinate and real source at each real band anchor. -/
theorem continuousAt_sourceAbelianPrimitive_complex_real_band
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (m : ℤ) (a : ℝ)
    (ha : a ∈ sourceRealBand hp hp1 φ.val m) :
    ContinuousAt (fun t : ℂ × realTypeSourceSubmodule p =>
      sourceAbelianPrimitive hp hp1 t.2.val t.2.property t.1) ((a : ℂ),φ) := by
  obtain ⟨r,hr,_,hcharts⟩ := exists_sourceAbelianLogChart_band_product hp hp1 φ m a ha
  have hm : Continuous (fun t : ℂ × realTypeSourceSubmodule p => (t.1,t.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hbase : ((a : ℂ),φ.val) ∈ Metric.ball (a : ℂ) r ×ˢ Metric.ball φ.val r :=
    ⟨Metric.mem_ball_self hr,Metric.mem_ball_self hr⟩
  have hc : ContinuousAt (fun t : ℂ × realTypeSourceSubmodule p =>
      sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) 0 (t.1,t.2.val)) ((a : ℂ),φ) := by
    simpa only [Function.comp_def] using!
      (((hcharts 0).1 ((a : ℂ),φ.val) hbase).continuousAt.comp
        (f := fun t : ℂ × realTypeSourceSubmodule p => (t.1,t.2.val))
        (hm.continuousAt (x := ((a : ℂ),φ))))
  apply hc.congr_of_eventuallyEq
  have hb := (hm.continuousAt (x := ((a : ℂ),φ))).tendsto.eventually
    ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hbase)
  filter_upwards [hb] with t ht
  simpa only [Int.cast_zero,mul_zero,add_zero] using
    ((hcharts 0).2.2 t.2 ht.2 t.1 ht.1).symm

end NLS.ZakharovShabat
