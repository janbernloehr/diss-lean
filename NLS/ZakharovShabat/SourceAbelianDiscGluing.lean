import NLS.ZakharovShabat.SourceAbelianDiscPrimitive
import NLS.ZakharovShabat.SourceAbelianHalfPlane
import NLS.ComplexAnalysis.NormalizedSegmentPrimitiveUnique

/-! # Matching the normalized abelian primitives across a selected gap

A single primitive on an isolating disc minus its gap agrees with the
endpoint-normalized primitives on both half-planes. Its full relative
limits at both endpoints are zero, including at a collapsed gap.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Localizing at a real point inside a disc does not lose the
nontrivial approaches from either half-plane. -/
theorem nhdsWithin_ball_sourceAbelianHalfPlane_neBot
    (c a : ℂ) (R : ℝ) (ha : a ∈ ball c R) (hareal : a.im = 0) (upper : Bool) :
    NeBot (𝓝[ball c R ∩ sourceAbelianHalfPlane upper] a) := by
  rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (isOpen_ball.mem_nhds ha))]
  exact nhdsWithin_sourceAbelianHalfPlane_neBot upper a hareal

/-- A left-normalized disc primitive agrees with either independently
constructed half-plane primitive wherever both are defined. -/
theorem sourceAbelian_discPrimitive_eq_halfPlane
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 φ n,
      HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
        sourceCanonicalRoot hp hp1 φ z) z)
    (hFl : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 φ n]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0))
    (upper : Bool) :
    EqOn F (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (ball c R ∩ sourceAbelianHalfPlane upper) := by
  have hl := (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).1
  let := nhdsWithin_ball_sourceAbelianHalfPlane_neBot c _ R
    (hseg (left_mem_segment ℝ _ _)) hl upper
  have hsub : ball c R ∩ sourceAbelianHalfPlane upper ⊆
      ball c R \ sourcePeriodicSegment hp hp1 φ n := fun z hz =>
    ⟨hz.1,(sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ upper hz.2) n⟩
  have hs := sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper
  exact primitives_eq_of_common_boundary_limit _ F _ _ _ 0
    (isOpen_ball.inter (isOpen_sourceAbelianHalfPlane upper))
    ((convex_ball c R).inter (convex_sourceAbelianHalfPlane upper)).isPreconnected
    (fun z hz => hF z (hsub hz)) (fun z hz => hs.1 z hz.2)
    (hFl.mono_left (nhdsWithin_mono _ hsub))
    (hs.2.1.mono_left (nhdsWithin_mono _ inter_subset_right))

/-- A finite right endpoint value of a left-normalized disc primitive
must also be zero, by comparison with the upper half-plane. -/
theorem sourceAbelian_discPrimitive_right_limit_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 φ n,
      HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
        sourceCanonicalRoot hp hp1 φ z) z)
    (hFl : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 φ n]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0))
    (B : ℂ) (hFr : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 φ n]
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 B)) :
    B = 0 := by
  have hr := (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).2
  let := nhdsWithin_ball_sourceAbelianHalfPlane_neBot c _ R
    (hseg (right_mem_segment ℝ _ _)) hr true
  have hsub : ball c R ∩ sourceAbelianHalfPlane true ⊆
      ball c R \ sourcePeriodicSegment hp hp1 φ n := fun z hz =>
    ⟨hz.1,(sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ true hz.2) n⟩
  have hmatch := sourceAbelian_discPrimitive_eq_halfPlane hp hp1 φ hφ n c R hseg F hF hFl true
  have hzero : Tendsto F
      (𝓝[ball c R ∩ sourceAbelianHalfPlane true]
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0) := by
    apply ((sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n true).2.2.mono_left
      (nhdsWithin_mono _ inter_subset_right)).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hmatch hz).symm
  exact tendsto_nhds_unique (hFr.mono_left (nhdsWithin_mono _ hsub)) hzero

/-- An isolating chart for the normalized Section 19 abelian integral.
The derivative and both endpoint limits concern the entire cut disc. -/
structure SourceAbelianDiscPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) where
  center : ℂ
  radius : ℝ
  toFun : ℂ → ℂ
  segment_subset : sourcePeriodicSegment hp hp1 φ n ⊆ ball center radius
  avoids_other : closedBall center radius ⊆ sourceStandardRootOmittedDomain hp hp1 φ n
  hasDerivAt : ∀ z ∈ ball center radius \ sourcePeriodicSegment hp hp1 φ n,
    HasDerivAt toFun (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
      sourceCanonicalRoot hp hp1 φ z) z
  left_limit : Tendsto toFun (𝓝[ball center radius \ sourcePeriodicSegment hp hp1 φ n]
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0)
  right_limit : Tendsto toFun (𝓝[ball center radius \ sourcePeriodicSegment hp hp1 φ n]
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0)

/-- Every real source and signed index admit an actual normalized chart,
including when the gap collapses to a removable point. -/
theorem nonempty_sourceAbelianDiscPrimitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    Nonempty (SourceAbelianDiscPrimitive hp hp1 φ hφ n) := by
  obtain ⟨c,R,hseg,hother,F,hF⟩ := exists_sourceAbelian_discComplement_primitive hp hp1 φ hφ n
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  by_cases hopen : l.re < r.re
  · obtain ⟨A,B,hA,hB⟩ := exists_sourceAbelian_discPrimitive_endpoint_limits hp hp1 φ hφ n c R
      hseg hother hopen F hF
    have hFl : Tendsto (fun z => F z-A)
        (𝓝[ball c R \ sourcePeriodicSegment hp hp1 φ n] l) (𝓝 0) := by
      simpa only [sub_self] using hA.sub_const A
    have hBA := sourceAbelian_discPrimitive_right_limit_eq_zero hp hp1 φ hφ n c R hseg
      (fun z => F z-A) (fun z hz => (hF z hz).sub_const A) hFl (B-A) (hB.sub_const A)
    exact ⟨⟨c,R,(fun z => F z-A),hseg,hother,
      (fun z hz => (hF z hz).sub_const A),hFl,by simpa only [hBA] using hB.sub_const A⟩⟩
  · have hle : l.re ≤ r.re := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 n)
    obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
    have he : l = r := Complex.ext (le_antisymm hle (le_of_not_gt hopen)) (hl.trans hr.symm)
    have hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0 := by
      rw [sourcePeriodicGapDisplacement_apply]
      exact sub_eq_zero.mpr he.symm
    obtain ⟨W,_,hrealW,hdata⟩ := exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
    have hg := hdata φ (hrealW hφ) n hgap
    obtain ⟨G,hG⟩ := exists_primitive_on_convex (sourceCriticalRootRatioExtension hp hp1 n φ)
      (ball c R) (convex_ball c R) isOpen_ball
      (hg.1.differentiableOn.mono (ball_subset_closedBall.trans hother))
    have hGn : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 φ n,
        HasDerivAt (fun z => G z-G l)
          (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z := by
      intro z hz
      rw [← hg.2 z (sourceAbelian_discComplement_subset_rootDomain hp hp1 φ n c R hother hz)]
      exact (hG z hz.1).sub_const (G l)
    have hGl : Tendsto (fun z => G z-G l)
        (𝓝[ball c R \ sourcePeriodicSegment hp hp1 φ n] l) (𝓝 0) := by
      simpa only [sub_self] using
        ((hG l (hseg (left_mem_segment ℝ _ _))).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds).sub_const (G l)
    refine ⟨⟨c,R,(fun z => G z-G l),hseg,hother,hGn,hGl,?_⟩⟩
    change Tendsto (fun z => G z-G l) (𝓝[ball c R \ sourcePeriodicSegment hp hp1 φ n] r) (𝓝 0)
    rwa [← he]

namespace SourceAbelianDiscPrimitive
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p}
  {hφ : IsRealType (CoeffPair.toMax p φ)} {n : ℤ}

/-- Both half-plane normalizations are the restrictions of one local function. -/
theorem eq_halfPlane (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) (upper : Bool) :
    EqOn D.toFun (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (ball D.center D.radius ∩ sourceAbelianHalfPlane upper) :=
  sourceAbelian_discPrimitive_eq_halfPlane hp hp1 φ hφ n D.center D.radius
    D.segment_subset D.toFun D.hasDerivAt D.left_limit upper

/-- Disc choices and primitive choices give identical normalized values
on every overlap, including for collapsed cuts. -/
theorem eqOn_overlap (D E : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    EqOn D.toFun E.toFun
      ((ball D.center D.radius ∩ ball E.center E.radius) \ sourcePeriodicSegment hp hp1 φ n) := by
  simpa only [sub_zero] using! normalized_segment_primitives_eq_on_convex_overlap _ D.toFun E.toFun
    (ball D.center D.radius) (ball E.center E.radius) _ _ 0 0
    isOpen_ball isOpen_ball (convex_ball _ _) (convex_ball _ _)
    (D.segment_subset (left_mem_segment ℝ _ _)) (E.segment_subset (left_mem_segment ℝ _ _))
    D.hasDerivAt E.hasDerivAt D.left_limit E.left_limit

end SourceAbelianDiscPrimitive
end NLS.ZakharovShabat
