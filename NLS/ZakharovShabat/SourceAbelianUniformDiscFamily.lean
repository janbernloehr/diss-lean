import NLS.ZakharovShabat.SourceAbelianContinuedProperties
import NLS.ZakharovShabat.SourcePsiGlobalContourFamily
import NLS.ZakharovShabat.SourceMidpointGradientTail
import NLS.ComplexAnalysis.LocallyFiniteLatticeDiscs

/-! # One source ball for all abelian continuation discs

The all-index contour family gives a smaller enclosing radius inside
each assigned disc. The source ball is chosen once for the entire
family, rather than by intersecting infinitely many neighborhoods.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceAbelianUniformDiscFamily (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) where
  source : realTypeSourceSubmodule p
  sourceRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  source_subset : ball source.val sourceRadius ⊆ W
  center : ℤ → ℂ
  inner : ℤ → ℝ
  outer : ℤ → ℝ
  inner_pos : ∀ j, 0 < inner j
  inner_lt : ∀ j, inner j < outer j
  disjoint : ∀ i j, i ≠ j → Disjoint (ball (center i) (outer i)) (ball (center j) (outer j))
  locallyFinite : LocallyFinite (fun j => closedBall (center j) (outer j))
  segment_subset : ∀ ψ ∈ ball source.val sourceRadius, ∀ j,
    sourcePeriodicSegment hp hp1 ψ j ⊆ ball (center j) (inner j)
  avoids_other : ∀ ψ ∈ ball source.val sourceRadius, ∀ j,
    closedBall (center j) (outer j) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j

/-- The entire infinite disc family exists on one source ball at every
real source in a prescribed open neighborhood. -/
theorem exists_sourceAbelianUniformDiscFamily (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (φ : realTypeSourceSubmodule p) (hφW : φ.val ∈ W) :
    ∃ D : SourceAbelianUniformDiscFamily hp hp1 W, D.source = φ := by
  obtain ⟨N,ε,hε,_,_,V,hV,hφV,c,R,_,_,hcluster,hdisjoint,hfilled,hdata⟩ :=
    exists_local_sourcePsi_allGap_realCenteredContourFamily_with_isolatingDiscs hp hp1 φ.val φ.property
  let C := sourceIsolatingCenter hp hp1 φ.val N
  let T := sourceIsolatingRadius hp hp1 φ.val N ε
  have hinner (j : ℤ) : ∃ r : ℝ, 0 < r ∧ r < T j ∧ closedBall (c j) (R j) ⊆ ball (C j) r := by
    apply exists_inner_radius_of_isCompact_subset_ball _ _ _ (isCompact_closedBall _ _)
      ⟨c j,mem_closedBall_self (hdata φ.val hφV j).1.le⟩
    simpa only [C,T,sourceIsolatingDisc_eq_ball] using hfilled j
  choose r hr hrT hinside using hinner
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp ((hV.inter hW).mem_nhds ⟨hφV,hφW⟩)
  have hlocal : LocallyFinite (fun j => closedBall (C j) (T j)) := by
    apply locallyFinite_closedBall_of_lattice_tail C T N Real.pi (Real.pi/4) Real.pi_pos
    intro j hj
    simp only [C,T,sourceIsolatingCenter,sourceIsolatingRadius,if_neg (not_le.mpr hj)]
    exact ⟨trivial,le_rfl⟩
  refine ⟨{
    source := φ
    sourceRadius := δ
    sourceRadius_pos := hδ
    source_subset := fun ψ hψ => (hδsub hψ).2
    center := C
    inner := r
    outer := T
    inner_pos := hr
    inner_lt := hrT
    disjoint := ?_
    locallyFinite := hlocal
    segment_subset := ?_
    avoids_other := ?_
  },rfl⟩
  · intro i j hij
    simpa only [C,T,sourceIsolatingDisc_eq_ball] using hdisjoint i j hij
  · intro ψ hψ j
    exact ((hdata ψ (hδsub hψ).1 j).2.1).trans (ball_subset_closedBall.trans (hinside j))
  · intro ψ hψ j
    have h := closure_sourceIsolatingDisc_subset_omittedDomain hp hp1 φ.val ψ N ε
      (hcluster ψ (hδsub hψ).1) hdisjoint j
    simpa only [sourceIsolatingDisc_eq_ball,closure_ball _ (ne_of_gt (sourceIsolatingRadius_pos hp hp1 φ.val N ε hε j))] using! h

namespace SourceAbelianUniformDiscFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def exterior (D : SourceAbelianUniformDiscFamily hp hp1 W) : Set ℂ :=
  (⋃ j, closedBall (D.center j) (D.inner j))ᶜ

theorem isOpen_exterior (D : SourceAbelianUniformDiscFamily hp hp1 W) : IsOpen D.exterior :=
  ((D.locallyFinite.subset (fun j => closedBall_subset_closedBall (D.inner_lt j).le)).isClosed_iUnion
    (fun _ => isClosed_closedBall)).isOpen_compl

theorem projectionPath_mem_ball (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    sourceRealProjectionPath hp ψ s ∈ ball D.source.val D.sourceRadius := by
  have h := sourceSegmentMap_mem (univ : Set ℂ) (ball D.source.val D.sourceRadius)
    (sourceRealTypeProjection hp ψ).val (convex_ball _ _)
    (sourceRealTypeProjection_mem_ball hp D.source D.sourceRadius ψ hψ) (0,ψ) ⟨mem_univ _,hψ⟩ s hs
  simpa only [sourceSegmentMap,Complex.coe_smul,sourceRealProjectionPath] using! h.2

/-- The common open exterior has a projected primitive for every
source in the one ball, including all distant spectral indices. -/
theorem exterior_product_subset_projected (D : SourceAbelianUniformDiscFamily hp hp1 W) :
    D.exterior ×ˢ ball D.source.val D.sourceRadius ⊆ sourceAbelianProjectedDomain hp hp1 W := by
  intro t ht s hs
  have hψ := D.projectionPath_mem_ball t.2 ht.2 s hs
  change (t.1,sourceRealProjectionPath hp t.2 s) ∈ sourceCanonicalRootJointDomain hp hp1 W
  refine ⟨D.source_subset hψ,?_⟩
  intro j hj
  exact ht.1 (mem_iUnion.mpr ⟨j,ball_subset_closedBall (D.segment_subset _ hψ j hj)⟩)

/-- Every annular collar lies in that same open exterior. -/
theorem collar_subset_exterior (D : SourceAbelianUniformDiscFamily hp hp1 W) (j : ℤ) :
    ball (D.center j) (D.outer j) \ closedBall (D.center j) (D.inner j) ⊆ D.exterior := by
  intro z hz hbad
  obtain ⟨k,hk⟩ := mem_iUnion.mp hbad
  by_cases he : k = j
  · subst k
    exact hz.2 hk
  · exact Set.disjoint_left.mp (D.disjoint j k (fun h => he h.symm)) hz.1 (closedBall_subset_ball (D.inner_lt k) hk)

/-- The common exterior and the cut discs cover the entire moving
cut complement at every source in the ball. -/
theorem rootDomain_eq_union (D : SourceAbelianUniformDiscFamily hp hp1 W) (ψ : CoeffPair p)
    (hψ : ψ ∈ ball D.source.val D.sourceRadius) :
    sourceCanonicalRootDomain hp hp1 ψ = D.exterior ∪
      ⋃ j : ℤ, ball (D.center j) (D.outer j) \ sourcePeriodicSegment hp hp1 ψ j := by
  ext z
  constructor
  · intro hz
    by_cases he : z ∈ D.exterior
    · exact Or.inl he
    · have hin : z ∈ ⋃ j, closedBall (D.center j) (D.inner j) := not_not.mp he
      obtain ⟨j,hj⟩ := mem_iUnion.mp hin
      exact Or.inr (mem_iUnion.mpr ⟨j,closedBall_subset_ball (D.inner_lt j) hj,hz j⟩)
  · rintro (hz | hz)
    · intro j hj
      exact hz (mem_iUnion.mpr ⟨j,ball_subset_closedBall (D.segment_subset ψ hψ j hj)⟩)
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      exact sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j (D.center j) (D.outer j) (D.avoids_other ψ hψ j) hj

end SourceAbelianUniformDiscFamily
end NLS.ZakharovShabat
