import NLS.ZakharovShabat.SourcePsiIsolatingLocalBranches
import NLS.ZakharovShabat.SourcePsiComplexRootDomain

/-!
# A common complex root atlas with spectral isolation

Choose the uniformly placed local branches inside any prescribed open
neighborhood of the real locus. Their glued atlas retains the local
isolating discs and lies in that neighborhood. Filling the omitted root
with the moving periodic midpoint places the entire root sequence in
the same disc family.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourcePsiIsolatingComplexRootAtlas (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) extends SourcePsiComplexRootAtlas hp hp1 where
  cutoff : realTypeSourceLocus p → ℕ
  enlargement : realTypeSourceLocus p → ℝ
  enlargement_pos : ∀ φ, 0 < enlargement φ
  enlargement_le : ∀ φ, enlargement φ ≤ Real.pi/4
  sourceBall_subset : ∀ φ, toSourcePsiComplexRootAtlas.sourceBall φ ⊆ U
  clusters : ∀ φ, ∀ ψ ∈ toSourcePsiComplexRootAtlas.sourceBall φ, ∀ m : ℤ,
    sourceSpectralCluster hp hp1 ψ m ⊆ sourceIsolatingDisc hp hp1 φ.val (cutoff φ) (enlargement φ) m
  disjoint : ∀ φ, ∀ i j : ℤ, i ≠ j →
    Disjoint (sourceIsolatingDisc hp hp1 φ.val (cutoff φ) (enlargement φ) i)
      (sourceIsolatingDisc hp hp1 φ.val (cutoff φ) (enlargement φ) j)
  placement : ∀ φ, ∀ n : ℤ, ∀ ψ ∈ toSourcePsiComplexRootAtlas.sourceBall φ,
    (localBranch φ).branch n ψ ∈ sourcePsiRootPlacementSet hp hp1 φ.val (cutoff φ) (enlargement φ) n

theorem nonempty_sourcePsiIsolatingComplexRootAtlas
    (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hreal : realTypeSourceLocus p ⊆ U) :
    Nonempty (SourcePsiIsolatingComplexRootAtlas hp hp1 U) := by
  classical
  let L := fun φ : realTypeSourceLocus p => Classical.choice
    (nonempty_sourcePsiIsolatingLocalBranches hp hp1 φ U hU (hreal φ.property))
  exact ⟨{
    tube := fun φ => (L φ).tube,
    localBranch := fun φ => (L φ).family,
    cutoff := fun φ => (L φ).cutoff,
    enlargement := fun φ => (L φ).enlargement,
    enlargement_pos := fun φ => (L φ).enlargement_pos,
    enlargement_le := fun φ => (L φ).enlargement_le,
    sourceBall_subset := fun φ => (L φ).sourceBall_subset,
    clusters := fun φ => (L φ).clusters,
    disjoint := fun φ => (L φ).disjoint,
    placement := fun φ => (L φ).placement
  }⟩

namespace SourcePsiIsolatingComplexRootAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
  (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U)

theorem domain_subset : A.toSourcePsiComplexRootAtlas.domain ⊆ U := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact A.sourceBall_subset φ hφ

theorem global_placement (φ : realTypeSourceLocus p) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.sourceBall φ) :
    A.toSourcePsiComplexRootAtlas.branch n ψ ∈
      sourcePsiRootPlacementSet hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) n := by
  rw [A.toSourcePsiComplexRootAtlas.eq_local n φ hψ]
  exact A.placement φ n ψ hψ

theorem filled_placement (φ : realTypeSourceLocus p) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.sourceBall φ) :
    ∃ ξ : ℂ, ξ ∈ sourcePeriodicSegment hp hp1 ψ n ∧
      ∀ m : ℤ, displacedRoots
        (sourcePsiFillDeletedRoot n (A.toSourcePsiComplexRootAtlas.branch n ψ) ξ) m ∈
          sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m := by
  refine ⟨sourceStandardRootMidpoint hp hp1 ψ n,?_,?_⟩
  · simpa only [sourceStandardRootMidpoint] using sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  intro m
  by_cases hmn : m = n
  · subst m
    rw [displacedRoots_sourcePsiFillDeletedRoot_same]
    apply sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ) n
      (A.clusters φ ψ hψ n)
    simpa only [sourceStandardRootMidpoint] using sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
    exact A.global_placement φ n ψ hψ m hmn

end SourcePsiIsolatingComplexRootAtlas
end NLS.ZakharovShabat
