import NLS.ZakharovShabat.SourceAbelianCauchyPrimitive

/-! # Uniform Cauchy charts around complex spectral gaps

A fixed collar of the old joint domain supplies the Cauchy density.
One source neighborhood supports the selected root and regular numerator,
including when the selected real gap collapses.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceAbelianCauchyChart (hp : p ≠ ⊤) (hp1 : 1 < p) (j : ℤ) where
  sources : Set (CoeffPair p)
  sources_open : IsOpen sources
  center : ℂ
  inner : ℝ
  radius : ℝ
  inner_pos : 0 < inner
  inner_lt : inner < radius
  anchor : ℂ
  anchor_mem : anchor ∈ ball center radius \ closedBall center inner
  segment_subset : ∀ ψ ∈ sources, sourcePeriodicSegment hp hp1 ψ j ⊆ ball center inner
  avoids_other : ∀ ψ ∈ sources, closedBall center radius ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j
  collar_joint : ∀ ψ ∈ sources, ∀ z ∈ closedBall center radius \ ball center inner,
    (z,ψ) ∈ sourceAbelianJointDomain hp hp1
  root_analytic : AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceStandardRoot hp hp1 t.2 j t.1)
    {t | t.2 ∈ sources ∧ t.1 ∉ sourcePeriodicSegment hp hp1 t.2 j}
  extension_analytic : ∀ ψ ∈ sources, AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 j ψ)
    (sourceStandardRootOmittedDomain hp hp1 ψ j)

namespace SourceAbelianCauchyChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {j : ℤ}

def restrict (D : SourceAbelianCauchyChart hp hp1 j) (V : Set (CoeffPair p)) (hV : IsOpen V) (hVD : V ⊆ D.sources) :
    SourceAbelianCauchyChart hp hp1 j where
  sources := V
  sources_open := hV
  center := D.center
  inner := D.inner
  radius := D.radius
  inner_pos := D.inner_pos
  inner_lt := D.inner_lt
  anchor := D.anchor
  anchor_mem := D.anchor_mem
  segment_subset ψ hψ := D.segment_subset ψ (hVD hψ)
  avoids_other ψ hψ := D.avoids_other ψ (hVD hψ)
  collar_joint ψ hψ := D.collar_joint ψ (hVD hψ)
  root_analytic := D.root_analytic.mono (fun _ ht => ⟨hVD ht.1,ht.2⟩)
  extension_analytic ψ hψ := D.extension_analytic ψ (hVD hψ)

theorem radius_pos (D : SourceAbelianCauchyChart hp hp1 j) : 0 < D.radius := D.inner_pos.trans D.inner_lt

theorem circle_joint (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) (hψ : ψ ∈ D.sources)
    (z : ℂ) (hz : z ∈ sphere D.center D.radius) : (z,ψ) ∈ sourceAbelianJointDomain hp hp1 := by
  apply D.collar_joint ψ hψ z ⟨sphere_subset_closedBall hz,?_⟩
  intro hi
  have he := mem_sphere.mp hz
  have hlt := mem_ball.mp hi
  linarith [D.inner_lt]

theorem anchor_joint (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) :
    (D.anchor,ψ) ∈ sourceAbelianJointDomain hp hp1 :=
  D.collar_joint ψ hψ D.anchor ⟨ball_subset_closedBall D.anchor_mem.1,
    fun h => D.anchor_mem.2 (ball_subset_closedBall h)⟩

theorem segment_subset_outer (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) :
    sourcePeriodicSegment hp hp1 ψ j ⊆ ball D.center D.radius :=
  (D.segment_subset ψ hψ).trans (ball_subset_ball D.inner_lt.le)

theorem anchor_off_segment (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) :
    D.anchor ∉ sourcePeriodicSegment hp hp1 ψ j :=
  fun h => D.anchor_mem.2 (ball_subset_closedBall (D.segment_subset ψ hψ h))

theorem quotient_analytic (D : SourceAbelianCauchyChart hp hp1 j) :
    AnalyticOnNhd ℂ (sourceAbelianCauchyQuotient hp hp1 j D.center D.radius) (ball D.center D.radius ×ˢ D.sources) := by
  apply sourceAbelianCauchyQuotient_analytic hp hp1 j D.center D.radius D.radius_pos.le D.sources D.sources_open
    (fun t ht => D.circle_joint t.2 ht.2 t.1 ht.1)
  intro t ht
  exact D.root_analytic t ⟨ht.2,(sourceAbelianJointDomain_subset_rootDomain hp hp1 t (D.circle_joint t.2 ht.2 t.1 ht.1)) j⟩

theorem quotient_slice_analytic (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) :
    AnalyticOnNhd ℂ (fun z => sourceAbelianCauchyQuotient hp hp1 j D.center D.radius (z,ψ)) (ball D.center D.radius) := by
  intro z hz
  exact (D.quotient_analytic (z,ψ) ⟨hz,hψ⟩).comp (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)

theorem primitive_hasDerivAt (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) (hψ : ψ ∈ D.sources)
    (z : ℂ) (hz : z ∈ ball D.center D.radius \ sourcePeriodicSegment hp hp1 ψ j) :
    HasDerivAt (fun w => sourceAbelianCauchyPrimitive hp hp1 j D.center D.radius (w,ψ))
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z :=
  sourceAbelianCauchyPrimitive_hasDerivAt hp hp1 ψ j D.center D.radius D.radius_pos (D.circle_joint ψ hψ)
    (D.avoids_other ψ hψ) (D.extension_analytic ψ hψ) (D.quotient_slice_analytic ψ hψ) z hz

/-- The constant separating the actual collar normalization from the
 Cauchy primitive is defined at one fixed regular spectral anchor. -/
def offset (D : SourceAbelianCauchyChart hp hp1 j) (ψ : CoeffPair p) : ℂ :=
  sourceAbelianJointPrimitive hp hp1 0 (D.anchor,ψ) - sourceAbelianCauchyPrimitive hp hp1 j D.center D.radius (D.anchor,ψ)

theorem offset_analytic (D : SourceAbelianCauchyChart hp hp1 j) : AnalyticOnNhd ℂ D.offset D.sources := by
  intro ψ hψ
  have hF := (sourceAbelianJointPrimitive_analytic hp hp1 0 (D.anchor,ψ) (D.anchor_joint ψ hψ)).comp
    (f := fun χ : CoeffPair p => (D.anchor,χ)) (analyticAt_const.prod analyticAt_id)
  have hQ := (D.root_analytic (D.anchor,ψ) ⟨hψ,D.anchor_off_segment ψ hψ⟩).comp
    (f := fun χ : CoeffPair p => (D.anchor,χ)) (analyticAt_const.prod analyticAt_id)
  have hH := (D.quotient_analytic (D.anchor,ψ) ⟨D.anchor_mem.1,hψ⟩).comp
    (f := fun χ : CoeffPair p => (D.anchor,χ)) (analyticAt_const.prod analyticAt_id)
  exact hF.sub (hQ.mul hH)

end SourceAbelianCauchyChart

/-- A Cauchy chart exists at every real potential and every selected gap,
 with no nondegeneracy assumption on that gap. -/
theorem exists_sourceAbelianCauchyChart (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (j : ℤ) :
    ∃ D : SourceAbelianCauchyChart hp hp1 j, φ.val ∈ D.sources := by
  obtain ⟨V,hV,hφV,c,r,T,hr,hrT,hdata⟩ := exists_local_sourceAbelian_complexDisc_continuation hp hp1 φ j
  obtain ⟨W,hW,_,hreal,hstd⟩ := exists_global_source_analytic_standardRoot hp hp1
  obtain ⟨E,hE,hrealE,hext⟩ := exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  let R := (r+T)/2
  have hrR : r < R := by dsimp [R]; linarith
  have hRT : R < T := by dsimp [R]; linarith
  let a : ℂ := c+(((r+R)/2 : ℝ) : ℂ)
  have hdist : dist a c = (r+R)/2 := by
    simp only [a,dist_eq_norm,add_sub_cancel_left,norm_real,Real.norm_eq_abs]
    exact abs_of_pos (by linarith)
  have ha : a ∈ ball c R \ closedBall c r := by
    constructor
    · rw [mem_ball,hdist]; linarith
    · rw [mem_closedBall,hdist]; linarith
  refine ⟨{
    sources := V ∩ (W ∩ E)
    sources_open := hV.inter (hW.inter hE)
    center := c
    inner := r
    radius := R
    inner_pos := hr
    inner_lt := hrR
    anchor := a
    anchor_mem := ha
    segment_subset := fun ψ hψ => (hdata ψ hψ.1).1
    avoids_other := fun ψ hψ => (closedBall_subset_closedBall hRT.le).trans (hdata ψ hψ.1).2.1
    collar_joint := fun ψ hψ z hz => (hdata ψ hψ.1).2.2.1 z ⟨(closedBall_subset_closedBall hRT.le) hz.1,hz.2⟩
    root_analytic := fun t ht => hstd t.2 ht.1.2.1 j t.1 ht.2
    extension_analytic := fun ψ hψ => hext ψ hψ.2.2 j
  },hφV,hreal φ.property,hrealE φ.property⟩

end NLS.ZakharovShabat
