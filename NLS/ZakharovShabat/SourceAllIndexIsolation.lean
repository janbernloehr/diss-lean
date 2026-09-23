import NLS.ZakharovShabat.SourceClusterDiscsLocal
import NLS.ZakharovShabat.SourceTailIsolation
import NLS.ZakharovShabat.FreeDiscSeparation

/-!
# One neighborhood for central and distant source clusters

A finite central index block uses discs frozen at a real-type base
potential. Every remaining index uses its free quarter-π disc. Both
containment statements hold on one open source neighborhood.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a real-type source potential, one open neighborhood supports
simultaneous central and high-index five-coordinate cluster isolation.
Central discs are mutually disjoint, as are the free tail discs. -/
theorem exists_local_source_all_index_cluster_isolation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
        (∀ ψ ∈ U, ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          sourceSpectralCluster hp hp1 ψ n ⊆
            sourceClusterDisc hp hp1 φ (fun _ => ε) n) ∧
        (∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
          sourceSpectralCluster hp hp1 ψ n ⊆ refinedResonantDisk n) ∧
        (∀ ψ ∈ U, ∀ n : ℤ,
          sourceSpectralCluster hp hp1 ψ n ⊆
            if n.natAbs ≤ N then sourceClusterDisc hp hp1 φ (fun _ => ε) n
            else refinedResonantDisk n) ∧
        (∀ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∀ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), i < j →
            Disjoint (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
              (sourceClusterDisc hp hp1 φ (fun _ => ε) j)) := by
  obtain ⟨N, Ut, hUto, hφt, htail⟩ := exists_uniform_source_tail_isolation hp hp1 φ
  obtain ⟨ε, hε, Uc, hUco, hφc, hcentral, hdisjoint⟩ :=
    exists_local_sourceClusterDiscs_finite_block hp hp1 φ hφ
      (Finset.Icc (-(N : ℤ)) (N : ℤ))
  refine ⟨N, ε, hε, Uc ∩ Ut, hUco.inter hUto, ⟨hφc, hφt⟩,
    ?_, ?_, ?_, hdisjoint⟩
  · intro ψ hψ n hn
    exact hcentral ψ hψ.1 n hn
  · intro ψ hψ n hn z hz
    obtain ⟨hL, hR, hD, hN, hC⟩ := htail ψ hψ.2 n hn
    rcases hz with h | h | h | h | h
    · rw [h]; exact hL
    · rw [h]; exact hR
    · rw [h]; exact hD
    · rw [h]; exact hN
    · rw [h]; exact hC
  · intro ψ hψ n
    by_cases hn : n.natAbs ≤ N
    · simp only [if_pos hn]
      have hmem : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      exact hcentral ψ hψ.1 n hmem
    · simp only [if_neg hn]
      have hnt : N < n.natAbs := by omega
      intro z hz
      obtain ⟨hL, hR, hD, hN, hC⟩ := htail ψ hψ.2 n hnt
      rcases hz with h | h | h | h | h
      · rw [h]; exact hL
      · rw [h]; exact hR
      · rw [h]; exact hD
      · rw [h]; exact hN
      · rw [h]; exact hC

end NLS.ZakharovShabat
