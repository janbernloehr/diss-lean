import NLS.ZakharovShabat.SourcePsiOriginalOmega
import NLS.ZakharovShabat.SourcePsiUniformFilledBranchStability

/-!
# Uniform placement of the analytic atlas in original isolating disks

Compactness gives one margin around the full real gap product inside any
supplied original disk family. Uniform stability of the analytic branches
then places every retained root and the moving-midpoint fill on one
source ball, independently of the omitted index. Restricting the source
neighborhood preserves the same original disks and comparison constant.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.originalGapProduct_margin
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (φ : CoeffPair p) (hφV : φ ∈ V) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ a ∈ sourcePeriodicGapRootSet hp hp1 φ,
      ball a μ ⊆ sourcePsiOriginalRootPlacement D := by
  have hsub : sourcePeriodicGapRootSet hp hp1 φ ⊆ sourcePsiOriginalRootPlacement D :=
    fun a ha m => hD.gap φ hφV m (ha m)
  obtain ⟨μ,hμ,hthick⟩ := (isCompact_sourcePeriodicGapRootSet hp hp1 φ).exists_cthickening_subset_open
    hD.isOpen_originalRootPlacement hsub
  exact ⟨μ,hμ,fun a ha b hb => hthick
    (mem_cthickening_of_dist_le b a μ (sourcePeriodicGapRootSet hp hp1 φ) ha (mem_ball.mp hb).le)⟩

/-- Every supplied original disk family places all atlas branches on one
source ball, including the moving-midpoint fill at the omitted coordinate. -/
theorem SourcePsiComplexRootAtlas.original_filled_placement_near_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourcePsiComplexRootAtlas hp hp1)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceLocus p) (hφV : φ.val ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ball φ.val δ ⊆ A.domain ∩ V ∧
      ∀ ψ ∈ ball φ.val δ, ∀ n : ℤ,
        sourcePsiFillDeletedRoot n (A.branch n ψ) (sourceStandardRootMidpoint hp hp1 ψ n) ∈
          sourcePsiOriginalRootPlacement D := by
  obtain ⟨μ,hμ,hmargin⟩ := hD.originalGapProduct_margin φ.val hφV
  obtain ⟨r,hr,hrS,hclose⟩ := (A.localBranch φ).exists_uniform_midpointFilled_graph_radius μ hμ
  obtain ⟨η,hη,hηV⟩ := Metric.isOpen_iff.mp hV φ.val hφV
  let δ := min r η
  have hδ : 0 < δ := lt_min hr hη
  have hlocal (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val δ) : ψ ∈ A.sourceBall φ :=
    ball_subset_ball ((min_le_left _ _).trans hrS) hψ
  refine ⟨δ,hδ,(fun ψ hψ => ⟨subset_iUnion A.sourceBall φ (hlocal ψ hψ),
    hηV (ball_subset_ball (min_le_right _ _) hψ)⟩),?_⟩
  intro ψ hψ n
  rw [A.eq_local n φ (hlocal ψ hψ)]
  have hbase := sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 φ n
  apply hmargin _ hbase
  have hb := hclose ψ (ball_subset_ball (min_le_left _ _) hψ) n
  exact (le_max_left _ _).trans_lt (by simpa only [Prod.dist_eq] using hb)

/-- The retained-coordinate version uses the same radius for every index. -/
theorem SourcePsiComplexRootAtlas.original_placement_near_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourcePsiComplexRootAtlas hp hp1)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceLocus p) (hφV : φ.val ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ball φ.val δ ⊆ A.domain ∩ V ∧
      ∀ ψ ∈ ball φ.val δ, ∀ n m : ℤ, m ≠ n →
        displacedRoots (A.branch n ψ:Coeff p) m ∈ D m := by
  obtain ⟨δ,hδ,hsub,hb⟩ := A.original_filled_placement_near_real hD hV φ hφV
  refine ⟨δ,hδ,hsub,?_⟩
  intro ψ hψ n m hmn
  simpa only [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn] using hb ψ hψ n m


/-- Restrict only the source neighborhood, retaining exactly the same disks. -/
theorem SourceIsolatingNeighborhoods.restrict_source
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V U : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hUV : U ⊆ V) :
    SourceIsolatingNeighborhoods hp hp1 U D c :=
  ⟨hD.one_le,hD.discs,fun ψ hψ => hD.cluster ψ (hUV hψ),
    fun ψ hψ => hD.gap ψ (hUV hψ),hD.pointwise_distance,hD.set_distance,hD.tail⟩

end NLS.ZakharovShabat
