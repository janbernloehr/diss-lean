import NLS.ZakharovShabat.AppendixFDeletedPair
import NLS.ComplexAnalysis.AppendixFCommonBoundary
import NLS.ZakharovShabat.SourceFullAbelianGapBoundary

/-! # Common source midpoint spokes for the collapsed-gap argument in F.2

The original isolating family excludes all other gaps, including at the
disc boundary. One fixed boundary point therefore works for every member
of a countable family of actual source potentials.
-/
noncomputable section
open Set Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
variable {D : ℤ → Set ℂ} {c : ℝ}

/-- Removing the selected gap from the closed isolating disc avoids every actual gap. -/
theorem SourceIsolatingNeighborhoods.closedCutDisk_subset_rootDomain
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    closure (D n) \ sourcePeriodicSegment hp hp1 ψ n ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  intro z hz m
  by_cases hm : m = n
  · subst m; exact hz.2
  · exact hD.closedDisk_subset_omittedDomain ψ hψ n hz.1 m hm

/-- A single original boundary point gives paths avoiding all gaps for a countable source family. -/
theorem SourceIsolatingNeighborhoods.exists_common_source_midpoint_spokes
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    {ι : Type*} [Countable ι] (ψ : ι → CoeffPair p) (hψ : ∀ k, ψ k ∈ V) (n : ℤ) :
    ∃ ν ∈ frontier (D n), ∀ k,
      ν ∈ sourceCanonicalRootDomain hp hp1 (ψ k) ∧
      segment ℝ (sourceStandardRootMidpoint hp hp1 (ψ k) n) ν \
        {sourceStandardRootMidpoint hp hp1 (ψ k) n} ⊆
          closure (D n) ∩ sourceCanonicalRootDomain hp hp1 (ψ k) := by
  obtain ⟨a,R,hR,he⟩ := hD.discs n
  have hmid (k : ι) : sourceStandardRootMidpoint hp hp1 (ψ k) n ∈ ball (a:ℂ) R := by
    rw [← he]
    exact hD.gap (ψ k) (hψ k) n (sourcePeriodicMidpoint_mem_segment hp hp1 (ψ k) n)
  obtain ⟨ν,hν,hpaths⟩ := appendixF_exists_common_midpoint_spokes (a:ℂ) R hR
    (fun k => sourceStandardRootMidpoint hp hp1 (ψ k) n)
    (fun k => sourceStandardRootHalfGap hp hp1 (ψ k) n)
    (fun k => ball_subset_closedBall (hmid k))
  have hpath (k : ι) :
      segment ℝ (sourceStandardRootMidpoint hp hp1 (ψ k) n) ν \
        {sourceStandardRootMidpoint hp hp1 (ψ k) n} ⊆
          closure (D n) ∩ sourceCanonicalRootDomain hp hp1 (ψ k) := by
    intro z hz
    have hh := hpaths k hz
    have hcl : z ∈ closure (D n) := by rw [he,closure_ball _ hR.ne']; exact hh.1
    exact ⟨hcl,hD.closedCutDisk_subset_rootDomain (ψ k) (hψ k) n
      ⟨hcl,by simpa only [sourcePeriodicSegment_eq_midpoint_segment] using hh.2⟩⟩
  refine ⟨ν,?_,?_⟩
  · rw [he,frontier_ball _ hR.ne']
    exact hν
  · intro k
    refine ⟨?_,hpath k⟩
    apply (hpath k ?_).2
    refine ⟨right_mem_segment ℝ _ _,?_⟩
    intro heq
    have hh : ν = sourceStandardRootMidpoint hp hp1 (ψ k) n := heq
    have hlt : dist ν (a:ℂ) < R := by rw [hh]; exact mem_ball.mp (hmid k)
    have heqR := mem_sphere.mp hν
    linarith

end NLS.ZakharovShabat
