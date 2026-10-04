import NLS.ZakharovShabat.SourceFullAbelianCauchyPrimitive

/-! # Cauchy constructions for all gaps on one source ball

A common real-centered source ball supports the full primitive, all selected
standard roots, and all regular numerator extensions. Each assigned spectral
disc therefore has a Cauchy construction without any gap-dependent shrinking
of the source ball.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceFullAbelianUniformCauchyFamily (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) where
  discs : SourceAbelianUniformDiscFamily hp hp1 W
  charts : ∀ ψ ∈ ball discs.source.val discs.sourceRadius, Nonempty (SourceAbelianSpectralChart hp hp1 W ψ)
  full_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
    (sourceCanonicalRootJointDomain hp hp1 (ball discs.source.val discs.sourceRadius))
  root_analytic : ∀ j : ℤ, AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceStandardRoot hp hp1 t.2 j t.1)
    {t | t.2 ∈ ball discs.source.val discs.sourceRadius ∧ t.1 ∉ sourcePeriodicSegment hp hp1 t.2 j}
  extension_analytic : ∀ ψ ∈ ball discs.source.val discs.sourceRadius, ∀ j : ℤ,
    AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 j ψ) (sourceStandardRootOmittedDomain hp hp1 ψ j)

/-- One ambient neighborhood supports common-ball Cauchy families
around every real source, simultaneously for the whole infinite gap family. -/
theorem exists_sourceFullAbelianUniformCauchyFamilies (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W, C.discs.source = φ := by
  obtain ⟨W,V,hW,hV,_,hreal,hVW,_,hcharts,hfull⟩ := exists_sourceFullAbelian_almostReal_jointAnalytic hp hp1
  obtain ⟨S,hS,_,hrealS,hstd⟩ := exists_global_source_analytic_standardRoot hp hp1
  obtain ⟨E,hE,hrealE,hext⟩ := exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  refine ⟨W,hW,hreal.trans hVW,?_⟩
  intro φ
  obtain ⟨D₀,hφ⟩ := exists_sourceAbelianUniformDiscFamily hp hp1 (V ∩ (S ∩ E))
    (hV.inter (hS.inter hE)) φ ⟨hreal φ.property,hrealS φ.property,hrealE φ.property⟩
  let D : SourceAbelianUniformDiscFamily hp hp1 W :=
    { D₀ with source_subset := fun ψ hψ => hVW (D₀.source_subset hψ).1 }
  refine ⟨{
    discs := D
    charts := fun ψ hψ => hcharts ψ (D₀.source_subset hψ).1
    full_analytic := fun n => (hfull n).mono (fun t ht => ⟨(D₀.source_subset ht.1).1,ht.2⟩)
    root_analytic := fun j t ht => hstd t.2 (D₀.source_subset ht.1).2.1 j t.1 ht.2
    extension_analytic := fun ψ hψ j => hext ψ (D₀.source_subset hψ).2.2 j
  },hφ⟩

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def anchor (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ) : ℂ :=
  Classical.choose (C.discs.collar_nonempty j)

theorem anchor_mem (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ) :
    C.anchor j ∈ ball (C.discs.center j) (C.discs.outer j) \ closedBall (C.discs.center j) (C.discs.inner j) :=
  Classical.choose_spec (C.discs.collar_nonempty j)

theorem anchor_root (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    C.anchor j ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  have ht : (C.anchor j,ψ) ∈ sourceAbelianProjectedDomain hp hp1 W :=
    C.discs.exterior_product_subset_projected ⟨C.discs.collar_subset_exterior j (C.anchor_mem j),hψ⟩
  exact (sourceAbelianProjectedDomain_end hp hp1 W ht).2

theorem circle_root (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (z : ℂ) (hz : z ∈ sphere (C.discs.center j) (C.discs.outer j)) :
    z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  intro k hk
  by_cases he : k = j
  · subst k
    have hlt := mem_ball.mp (C.discs.segment_subset ψ hψ j hk)
    rw [mem_sphere.mp hz] at hlt
    exact (not_lt_of_ge (C.discs.inner_lt j).le) hlt
  · exact C.discs.avoids_other ψ hψ j (sphere_subset_closedBall hz) k he hk

theorem segment_subset_outer (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    sourcePeriodicSegment hp hp1 ψ j ⊆ ball (C.discs.center j) (C.discs.outer j) :=
  (C.discs.segment_subset ψ hψ j).trans (ball_subset_ball (C.discs.inner_lt j).le)

theorem quotient_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ) :
    AnalyticOnNhd ℂ (sourceFullAbelianCauchyQuotient hp hp1 W j (C.discs.center j) (C.discs.outer j))
      (ball (C.discs.center j) (C.discs.outer j) ×ˢ ball C.discs.source.val C.discs.sourceRadius) := by
  apply sourceFullAbelianCauchyQuotient_analytic hp hp1 W j _ _
    ((C.discs.inner_pos j).trans (C.discs.inner_lt j)).le _ isOpen_ball
    (fun t ht => C.circle_root j t.2 ht.2 t.1 ht.1)
    ((C.full_analytic 0).mono (fun t ht => ⟨ht.2,C.circle_root j t.2 ht.2 t.1 ht.1⟩))
  exact fun t ht => C.root_analytic j t ⟨ht.2,C.circle_root j t.2 ht.2 t.1 ht.1 j⟩

theorem quotient_slice_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    AnalyticOnNhd ℂ (fun z => sourceFullAbelianCauchyQuotient hp hp1 W j (C.discs.center j) (C.discs.outer j) (z,ψ))
      (ball (C.discs.center j) (C.discs.outer j)) := by
  intro z hz
  exact (C.quotient_analytic j (z,ψ) ⟨hz,hψ⟩).comp (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)

theorem primitive_hasDerivAt (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (z : ℂ) (hz : z ∈ ball (C.discs.center j) (C.discs.outer j) \ sourcePeriodicSegment hp hp1 ψ j) :
    HasDerivAt (fun w => sourceFullAbelianCauchyPrimitive hp hp1 W j (C.discs.center j) (C.discs.outer j) (w,ψ))
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z := by
  obtain ⟨E⟩ := C.charts ψ hψ
  exact sourceFullAbelianCauchyPrimitive_hasDerivAt hp hp1 W ψ j _ _
    ((C.discs.inner_pos j).trans (C.discs.inner_lt j)) E (C.circle_root j ψ hψ)
    (C.discs.avoids_other ψ hψ j) (C.extension_analytic ψ hψ j) (C.quotient_slice_analytic j ψ hψ) z hz

def offset (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ) (ψ : CoeffPair p) : ℂ :=
  sourceFullAbelianPrimitive hp hp1 W 0 (C.anchor j,ψ) -
    sourceFullAbelianCauchyPrimitive hp hp1 W j (C.discs.center j) (C.discs.outer j) (C.anchor j,ψ)

theorem offset_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ) :
    AnalyticOnNhd ℂ (C.offset j) (ball C.discs.source.val C.discs.sourceRadius) := by
  intro ψ hψ
  have hF := (C.full_analytic 0 (C.anchor j,ψ) ⟨hψ,C.anchor_root j ψ hψ⟩).comp
    (f := fun χ : CoeffPair p => (C.anchor j,χ)) (analyticAt_const.prod analyticAt_id)
  have hQ := (C.root_analytic j (C.anchor j,ψ) ⟨hψ,C.anchor_root j ψ hψ j⟩).comp
    (f := fun χ : CoeffPair p => (C.anchor j,χ)) (analyticAt_const.prod analyticAt_id)
  have hH := (C.quotient_analytic j (C.anchor j,ψ) ⟨(C.anchor_mem j).1,hψ⟩).comp
    (f := fun χ : CoeffPair p => (C.anchor j,χ)) (analyticAt_const.prod analyticAt_id)
  exact hF.sub (hQ.mul hH)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
