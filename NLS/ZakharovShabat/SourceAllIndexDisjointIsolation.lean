import NLS.ZakharovShabat.SourceCentralTailSeparation
import NLS.ZakharovShabat.SourceAllIndexIsolation
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Pairwise disjoint source isolating discs at every signed index

The central discs use a margin at most π/4. Localizing the two outer
central periodic endpoints in their free discs separates the whole
central block from both tails, completing the all-index disc geometry.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The assigned disc at a signed index: a fixed central midpoint disc or
the free quarter-π disc outside the central block. -/
def sourceIsolatingDisc (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ) : Set ℂ :=
  if n.natAbs ≤ N then sourceClusterDisc hp hp1 φ (fun _ => ε) n
  else refinedResonantDisk n

/-- At a real-type source potential, one open neighborhood supports
pairwise disjoint isolating discs for every signed index, each containing
all five canonical coordinates of the nearby spectral cluster. -/
theorem exists_local_source_pairwise_disjoint_isolating_discs
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
        (∀ ψ ∈ U, ∀ n : ℤ,
          sourceSpectralCluster hp hp1 ψ n ⊆
            sourceIsolatingDisc hp hp1 φ N ε n) ∧
        (∀ i j : ℤ, i ≠ j →
          Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
            (sourceIsolatingDisc hp hp1 φ N ε j)) := by
  obtain ⟨N₀, Ut, hUto, hφt, htail⟩ := exists_uniform_source_tail_isolation hp hp1 φ
  let N := N₀ + 1
  have hN₀ : N₀ < N := by dsimp [N]; omega
  have hpos : N₀ < (N : ℤ).natAbs := by simpa using hN₀
  have hneg : N₀ < (-(N : ℤ)).natAbs := by simpa using hN₀
  have houterR := (htail φ hφt (N : ℤ) hpos).2.1
  have houterL := (htail φ hφt (-(N : ℤ)) hneg).1
  obtain ⟨ε, hε, hεmax, Uc, hUco, hφc, hcentral, hcentralDisjoint⟩ :=
    exists_local_sourceClusterDiscs_finite_block_bounded hp hp1 φ hφ
      (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (by positivity : 0 < Real.pi/4)
  refine ⟨N, ε, hε, hεmax, Uc ∩ Ut, hUco.inter hUto,
    ⟨hφc, hφt⟩, ?_, ?_⟩
  · intro ψ hψ n
    by_cases hn : n.natAbs ≤ N
    · simp only [sourceIsolatingDisc, if_pos hn]
      have hmem : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      exact hcentral ψ hψ.1 n hmem
    · simp only [sourceIsolatingDisc, if_neg hn]
      have hnt : N₀ < n.natAbs := by omega
      intro z hz
      obtain ⟨hL, hR, hD, hN, hC⟩ := htail ψ hψ.2 n hnt
      rcases hz with h | h | h | h | h
      · rw [h]; exact hL
      · rw [h]; exact hR
      · rw [h]; exact hD
      · rw [h]; exact hN
      · rw [h]; exact hC
  · intro i j hij
    by_cases hi : i.natAbs ≤ N
    · have hiIcc : i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      by_cases hj : j.natAbs ≤ N
      · have hjIcc : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          simp only [Finset.mem_Icc]
          omega
        simp only [sourceIsolatingDisc, if_pos hi, if_pos hj]
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact hcentralDisjoint i hiIcc j hjIcc hlt
        · exact (hcentralDisjoint j hjIcc i hiIcc hgt).symm
      · simp only [sourceIsolatingDisc, if_pos hi, if_neg hj]
        have hbounds : -(N : ℤ) ≤ i ∧ i ≤ (N : ℤ) := by
          simpa only [Finset.mem_Icc] using hiIcc
        have htailSide : j < -(N : ℤ) ∨ (N : ℤ) < j := by omega
        rcases htailSide with hleft | hright
        · exact sourceClusterDisc_disjoint_negative_tail hp hp1 φ hφ N ε
            hε.le hεmax houterL hbounds.1 hleft
        · exact sourceClusterDisc_disjoint_positive_tail hp hp1 φ hφ N ε
            hε.le hεmax houterR hbounds.2 hright
    · by_cases hj : j.natAbs ≤ N
      · have hjIcc : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          simp only [Finset.mem_Icc]
          omega
        simp only [sourceIsolatingDisc, if_neg hi, if_pos hj]
        have hbounds : -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ) := by
          simpa only [Finset.mem_Icc] using hjIcc
        have htailSide : i < -(N : ℤ) ∨ (N : ℤ) < i := by omega
        rcases htailSide with hleft | hright
        · exact (sourceClusterDisc_disjoint_negative_tail hp hp1 φ hφ N ε
            hε.le hεmax houterL hbounds.1 hleft).symm
        · exact (sourceClusterDisc_disjoint_positive_tail hp hp1 φ hφ N ε
            hε.le hεmax houterR hbounds.2 hright).symm
      · simpa only [sourceIsolatingDisc, if_neg hi, if_neg hj] using
          refinedResonantDisk_disjoint hij

/-- The common source neighborhood can be chosen open and connected by
shrinking it to a norm ball around the real-type base potential. -/
theorem exists_local_source_connected_isolating_discs
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ φ ∈ U ∧
        (∀ ψ ∈ U, ∀ n : ℤ,
          sourceSpectralCluster hp hp1 ψ n ⊆
            sourceIsolatingDisc hp hp1 φ N ε n) ∧
        (∀ i j : ℤ, i ≠ j →
          Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
            (sourceIsolatingDisc hp hp1 φ N ε j)) := by
  obtain ⟨N, ε, hε, hεmax, U, hUopen, hφU, hcluster, hdisjoint⟩ :=
    exists_local_source_pairwise_disjoint_isolating_discs hp hp1 φ hφ
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hφU)
  refine ⟨N, ε, hε, hεmax, ball φ r, Metric.isOpen_ball,
    isConnected_ball hr, mem_ball_self hr, ?_, hdisjoint⟩
  intro ψ hψ n
  exact hcluster ψ (hrU hψ) n

end NLS.ZakharovShabat
