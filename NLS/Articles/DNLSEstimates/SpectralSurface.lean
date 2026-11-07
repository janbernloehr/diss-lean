import NLS.Articles.DNLSEstimates.SpectralCurve
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# A complex analytic surface structure on the nonsingular spectral curve

Charts use one ambient coordinate, so every transition is an ambient
linear projection of an analytic inverse chart. The topology is the
original subspace topology in `ℂ × ℂ`.
-/
noncomputable section
open Set Complex Metric Filter Topology NLS.ZakharovShabat
open scoped Manifold ContDiff
namespace NLS.Articles.DNLSEstimates

/-- A coordinate chart whose inverse is analytic in the ambient plane. -/
structure AnalyticDoubleCoverChart (f : ℂ → ℂ) where
  chart : OpenPartialHomeomorph (doubleCover f) ℂ
  projection : (ℂ × ℂ) →L[ℂ] ℂ
  projection_eq : ∀ q, chart q = projection q.val
  inverse_analytic : AnalyticOnNhd ℂ (fun u => (chart.symm u).val) chart.target

/-- An actual local analytic graph produces an open chart in the
unchanged subspace topology, with both exact inverse identities. -/
theorem doubleCover_chart_of_graph (f : ℂ → ℂ) (q : doubleCover f)
    (k : (ℂ × ℂ) →L[ℂ] ℂ) (P : ℂ → ℂ × ℂ)
    (hP : AnalyticAt ℂ P (k q.val)) (hbase : P (k q.val) = q.val)
    (hproj : ∀ u, k (P u) = u)
    (hcurve : ∀ᶠ u in 𝓝 (k q.val), P u ∈ doubleCover f)
    (hgraph : ∀ᶠ x in 𝓝 q.val, x ∈ doubleCover f ↔ x = P (k x)) :
    ∃ C : AnalyticDoubleCoverChart f, q ∈ C.chart.source := by
  classical
  obtain ⟨U,hUeq,hU,hqU⟩ := _root_.eventually_nhds_iff.mp hgraph
  have ht : Tendsto P (𝓝 (k q.val)) (𝓝 q.val) := by
    simpa only [hbase] using hP.continuousAt.tendsto
  have hv := (ht.eventually (hU.mem_nhds hqU)).and (hcurve.and hP.eventually_analyticAt)
  obtain ⟨V,hVdata,hV,hqV⟩ := _root_.eventually_nhds_iff.mp hv
  let inv : ℂ → doubleCover f := fun u => if h : P u ∈ doubleCover f then ⟨P u,h⟩ else q
  have hinv (u : ℂ) (hu : u ∈ V) : (inv u).val = P u := by
    simp only [inv,dif_pos (hVdata u hu).2.1]
  have hPa : AnalyticOnNhd ℂ P V := fun u hu => (hVdata u hu).2.2
  let S : Set (doubleCover f) := {x | x.val ∈ U ∧ k x.val ∈ V}
  have hS : IsOpen S := (hU.preimage continuous_subtype_val).inter
    (hV.preimage (k.continuous.comp continuous_subtype_val))
  let e : OpenPartialHomeomorph (doubleCover f) ℂ := {
    toFun := fun x => k x.val
    invFun := inv
    source := S
    target := V
    map_source' := fun x hx => hx.2
    map_target' := by
      intro u hu
      change (inv u).val ∈ U ∧ k (inv u).val ∈ V
      rw [hinv u hu,hproj]
      exact ⟨(hVdata u hu).1,hu⟩
    left_inv' := by
      intro x hx
      apply Subtype.ext
      rw [hinv _ hx.2]
      exact ((hUeq x.val hx.1).mp x.property).symm
    right_inv' := by
      intro u hu
      rw [hinv u hu,hproj]
    open_source := hS
    open_target := hV
    continuousOn_toFun := (k.continuous.comp continuous_subtype_val).continuousOn
    continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      (hPa.continuousOn.congr hinv)
  }
  refine ⟨⟨e,k,fun _ => rfl,?_⟩,⟨hqU,hqV⟩⟩
  intro u hu
  apply (hPa u hu).congr
  filter_upwards [hV.mem_nhds hu] with v hv
  exact (hinv v hv).symm

/-- Every regular point has a chart, including the ramified spectral points. -/
theorem doubleCover_exists_chart (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (q : doubleCover f) (hreg : doubleCoverRegular f q.val) :
    ∃ C : AnalyticDoubleCoverChart f, q ∈ C.chart.source := by
  by_cases hw : q.val.2 = 0
  · have hz : f q.val.1 = 0 := by
      have h := q.property
      change q.val.2^2 = f q.val.1 at h
      rw [hw] at h
      simpa using h.symm
    have hd : deriv f q.val.1 ≠ 0 := by
      intro he
      exact hreg ((doubleCover_differential_zero_iff f q.val (hf _ (mem_univ _))).mpr ⟨hw,he⟩)
    obtain ⟨g,hg,hg0,hgc,hge⟩ := doubleCover_simple_uniformizer f q.val.1 (hf _ (mem_univ _)) hz hd
    let P : ℂ → ℂ × ℂ := fun u => (g (u^2),u)
    have hq : q.val = (q.val.1,0) := Prod.ext rfl hw
    apply doubleCover_chart_of_graph f q (ContinuousLinearMap.snd ℂ ℂ ℂ) P
    · change AnalyticAt ℂ P q.val.2
      rw [hw]
      have hg0a : AnalyticAt ℂ g ((0 : ℂ)^2) := by simpa only [zero_pow (by decide : 2 ≠ 0)] using hg
      exact (hg0a.comp (f := fun u : ℂ => u^2) (by fun_prop)).prod analyticAt_id
    · change (g (q.val.2^2),q.val.2) = q.val
      rw [hw]
      simpa only [zero_pow (by decide : 2 ≠ 0),hg0] using hq.symm
    · intro u; rfl
    · simpa only [ContinuousLinearMap.coe_snd',hw,P] using hgc
    · rw [hq]
      filter_upwards [hge] with x hx
      change x ∈ doubleCover f ↔ x = (g (x.2^2),x.2)
      rw [hx]
      exact ⟨fun h => Prod.ext h rfl,fun h => congrArg Prod.fst h⟩
  · obtain ⟨h,hh,hhz,hcurve,hgraph⟩ := doubleCover_unramified_graph f q.val.1 q.val.2
      (hf _ (mem_univ _)) hw q.property
    let P : ℂ → ℂ × ℂ := fun u => (u,h u)
    apply doubleCover_chart_of_graph f q (ContinuousLinearMap.fst ℂ ℂ ℂ) P
    · exact analyticAt_id.prod hh
    · exact Prod.ext rfl hhz
    · intro u; rfl
    · exact Filter.Eventually.of_forall hcurve
    · filter_upwards [hgraph] with x hx
      change x ∈ doubleCover f ↔ x = (x.1,h x.1)
      rw [hx]
      exact ⟨fun h => Prod.ext rfl h,fun h => congrArg Prod.snd h⟩

/-- Chart changes are analytic, since forward charts are ambient linear projections. -/
theorem AnalyticDoubleCoverChart.transition_analytic {f : ℂ → ℂ}
    (C D : AnalyticDoubleCoverChart f) :
    AnalyticOnNhd ℂ (C.chart.symm.trans D.chart) (C.chart.symm.trans D.chart).source := by
  intro u hu
  have ha := (D.projection.analyticAt (C.chart.symm u).val).comp
    (f := fun v : ℂ => (C.chart.symm v).val) (C.inverse_analytic u hu.1)
  apply ha.congr
  exact Filter.Eventually.of_forall fun v => (D.projection_eq (C.chart.symm v)).symm

/-- An atlas of the regular double cover in its actual subspace topology. -/
@[instance_reducible] def doubleCoverChartedSpace (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hr : ∀ q : doubleCover f, doubleCoverRegular f q.val) : ChartedSpace ℂ (doubleCover f) where
  atlas := {e | ∃ C : AnalyticDoubleCoverChart f, C.chart = e}
  chartAt := fun q => (Classical.choose (doubleCover_exists_chart f hf q (hr q))).chart
  mem_chart_source := fun q => Classical.choose_spec (doubleCover_exists_chart f hf q (hr q))
  chart_mem_atlas := fun q => ⟨Classical.choose (doubleCover_exists_chart f hf q (hr q)),rfl⟩

/-- The atlas gives a complex analytic one-dimensional manifold. -/
theorem doubleCover_isManifold (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hr : ∀ q : doubleCover f, doubleCoverRegular f q.val) :
    letI := doubleCoverChartedSpace f hf hr
    IsManifold 𝓘(ℂ,ℂ) ω (doubleCover f) := by
  let := doubleCoverChartedSpace f hf hr
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨C,rfl⟩ := he
  obtain ⟨D,rfl⟩ := he'
  simpa using (C.transition_analytic D).contDiffOn_of_completeSpace (n := ω)

/-- The actual simple periodic spectrum supplies the complex surface;
no smoothness of the source potential is required. -/
theorem spectralCurve_complex_surface {p : ENNReal} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p)
    (hsimple : ∀ z ∈ periodicSpectrum hp (periodOnePotential a),
      periodicAlgebraicMultiplicity hp (periodOnePotential a) z = 1) :
    ∃ c : ChartedSpace ℂ (spectralCurve hp a),
      @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ,ℂ) ω (spectralCurve hp a) _ c := by
  let f : ℂ → ℂ := fun z => (canonicalDiscriminant hp (periodOnePotential a) z)^2-4
  have hf : AnalyticOnNhd ℂ f univ := fun z _ =>
    ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem a) z (mem_univ _)).pow 2).sub analyticAt_const
  have hr : ∀ q : doubleCover f, doubleCoverRegular f q.val := fun q =>
    (spectralCurve_regular_iff_simple hp hp1 a).mpr hsimple q.val q.property
  exact ⟨doubleCoverChartedSpace f hf hr,doubleCover_isManifold f hf hr⟩



/-- The spectral projection onto the complex plane is onto. The second
coordinate supplies the square root on the curve itself. -/
theorem doubleCover_projection_surjective (f : ℂ → ℂ) :
    Function.Surjective (fun q : doubleCover f => q.val.1) := by
  intro z
  have hs : (Complex.sqrt (f z))^2 = f z := by
    have h := Complex.cpow_nat_inv_pow (f z) (by decide : 2 ≠ 0)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  exact ⟨⟨(z,Complex.sqrt (f z)),hs⟩,rfl⟩

/-- The affine double cover is noncompact in its original subspace topology. -/
theorem doubleCover_not_compact (f : ℂ → ℂ) : ¬ CompactSpace (doubleCover f) := by
  intro hc
  let := hc
  have hs : (fun q : doubleCover f => q.val.1) '' univ = (univ : Set ℂ) := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨q,rfl⟩ := doubleCover_projection_surjective f z
      exact mem_image_of_mem _ (mem_univ q)
  have hi := isCompact_univ.image (continuous_fst.comp continuous_subtype_val :
    Continuous (fun q : doubleCover f => q.val.1))
  change IsCompact ((fun q : doubleCover f => q.val.1) '' univ) at hi
  rw [hs] at hi
  obtain ⟨B,hB⟩ := hi.isBounded.exists_norm_le
  have hb := hB ((|B|+1 : ℝ) : ℂ) (mem_univ _)
  have hn : ‖((|B|+1 : ℝ) : ℂ)‖ = |B|+1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  rw [hn] at hb
  linarith [le_abs_self B]

/-- In particular, the actual spectral curve is an open, noncompact surface
when its spectrum is simple; compactness is not assumed in its atlas. -/
theorem spectralCurve_not_compact {p : ENNReal} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (a : CoeffPair p) : ¬ CompactSpace (spectralCurve hp a) :=
  doubleCover_not_compact _

end NLS.Articles.DNLSEstimates
