import NLS.ZakharovShabat.SourcePsiFullRootPlacement
import NLS.ZakharovShabat.SourcePsiUniformEquationTubeRestriction
import NLS.ZakharovShabat.SourcePsiComplexRootAtlas

/-!
# Uniform complex root branches in assigned isolating discs

At a real base source, shrink the actual equation tube to the common
root-placement margin and a prescribed open source neighborhood. The
quantitative branch construction then keeps every retained root in its
assigned disc, for all deleted indices on the same source ball. The
moving spectral clusters lie in that same pairwise disjoint disc family.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourcePsiIsolatingLocalBranches
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (U : Set (CoeffPair p)) where
  tube : SourcePsiUniformEquationTube hp hp1 φ
  family : SourcePsiUniformComplexBranchFamily tube
  cutoff : ℕ
  enlargement : ℝ
  enlargement_pos : 0 < enlargement
  enlargement_le : enlargement ≤ Real.pi/4
  sourceBall_subset : ball φ.val family.sourceRadius ⊆ U
  clusters : ∀ ψ ∈ ball φ.val family.sourceRadius, ∀ m : ℤ,
    sourceSpectralCluster hp hp1 ψ m ⊆ sourceIsolatingDisc hp hp1 φ.val cutoff enlargement m
  disjoint : ∀ i j : ℤ, i ≠ j →
    Disjoint (sourceIsolatingDisc hp hp1 φ.val cutoff enlargement i)
      (sourceIsolatingDisc hp hp1 φ.val cutoff enlargement j)
  placement : ∀ n : ℤ, ∀ ψ ∈ ball φ.val family.sourceRadius,
    family.branch n ψ ∈ sourcePsiRootPlacementSet hp hp1 φ.val cutoff enlargement n

theorem nonempty_sourcePsiIsolatingLocalBranches
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (hφ : φ.val ∈ U) :
    Nonempty (SourcePsiIsolatingLocalBranches hp hp1 φ U) := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,_,hφV,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ.val φ.property
  obtain ⟨η,hη,hηball⟩ := Metric.isOpen_iff.mp (hU.inter hVopen) φ.val ⟨hφ,hφV⟩
  have hgap (m : ℤ) : sourcePeriodicSegment hp hp1 φ.val m ⊆ sourceIsolatingDisc hp hp1 φ.val N ε m :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val φ.val N ε m (hcluster φ.val hφV m)
  obtain ⟨μ,hμ,hmargin⟩ := exists_uniform_fullRootPlacement_radius hp hp1 φ.val N ε hgap
  obtain ⟨D⟩ := nonempty_sourcePsiUniformEquationTube hp hp1 φ
  let r := min D.radius (min μ η)
  have hr : 0 < r := lt_min D.radius_pos (lt_min hμ hη)
  have hrD : r ≤ D.radius := min_le_left _ _
  have hrμ : r ≤ μ := (min_le_right _ _).trans (min_le_left _ _)
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  let E := D.restrictRadius r hr hrD
  obtain ⟨S⟩ := nonempty_sourcePsiUniformComplexBranchFamily E
  have hρr : S.rootRadius < r := S.rootRadius_lt
  have hδη : S.sourceRadius ≤ η := S.sourceRadius_le_rootRadius.trans (hρr.le.trans hrη)
  have hsource (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val S.sourceRadius) : ψ ∈ U ∩ V :=
    hηball (ball_subset_ball hδη hψ)
  refine ⟨{
    tube := E, family := S, cutoff := N, enlargement := ε,
    enlargement_pos := hε, enlargement_le := hεmax,
    sourceBall_subset := fun ψ hψ => (hsource ψ hψ).1,
    clusters := fun ψ hψ m => hcluster ψ (hsource ψ hψ).2 m,
    disjoint := hdisjoint, placement := ?_
  }⟩
  intro n ψ hψ
  let ξ := sourceStandardRootMidpoint hp hp1 φ.val n
  let a := sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ) ξ
  let b := sourcePsiFillDeletedRoot n (S.branch n ψ) ξ
  have ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ.val :=
    sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 φ n
  have hroot : dist (S.branch n ψ) (sourcePsiGapRoot hp hp1 n φ) < μ := by
    have h := S.graph n ψ hψ
    rw [mem_ball,Prod.dist_eq] at h
    exact ((le_max_left _ _).trans_lt h).trans_le (hρr.le.trans hrμ)
  have hdist : dist b a = dist (S.branch n ψ) (sourcePsiGapRoot hp hp1 n φ) := by
    simp only [b,a,sourcePsiFillDeletedRoot,dist_eq_norm,add_sub_add_right_eq_sub]
    rfl
  have hb : b ∈ sourcePsiFullRootPlacementSet hp hp1 φ.val N ε :=
    hmargin a ha (mem_ball.mpr (hdist.trans_lt hroot))
  intro m hmn
  have h := hb m
  simpa only [b,displacedRoots_sourcePsiFillDeletedRoot_other n m hmn] using h

end NLS.ZakharovShabat
