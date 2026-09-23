import NLS.ZakharovShabat.SourceClusterDiscs
import NLS.ZakharovShabat.CanonicalCriticalContinuity

/-!
# Local persistence of finite central source discs

At a real-type source potential, continuity of all five canonical
coordinates keeps each finite spectral cluster inside a disc frozen at
the base potential. A finite block shares one open source neighborhood.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A finite five-coordinate source cluster remains in any fixed open set
containing its base-point cluster. -/
theorem eventually_sourceSpectralCluster_subset_open
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (V : Set ℂ) (hV : IsOpen V)
    (hbase : sourceSpectralCluster hp hp1 φ n ⊆ V) :
    ∀ᶠ ψ : CoeffPair p in 𝓝 φ, sourceSpectralCluster hp hp1 ψ n ⊆ V := by
  let F : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  have hL := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hφ n).eventually
    (hV.mem_nhds (hbase (Or.inl rfl)))
  have hR := (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hφ n).eventually
    (hV.mem_nhds (hbase (Or.inr (Or.inl rfl))))
  have hD := (continuousAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ hφ n).eventually
    (hV.mem_nhds (hbase (Or.inr (Or.inr (Or.inl rfl)))))
  have hN := (continuousAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .neumann φ hφ n).eventually
    (hV.mem_nhds (hbase (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hc : ContinuousAt (fun ψ : CoeffPair p =>
      canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ := by
    exact (continuousAt_canonicalCriticalPoints_of_realType hp hp1 (F φ)
      (isRealType_periodOnePotential φ hφ) n).comp F.continuous.continuousAt
  have hC := hc.eventually
    (hV.mem_nhds (hbase (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  filter_upwards [hL, hR, hD, hN, hC] with ψ hLψ hRψ hDψ hNψ hCψ
  intro z hz
  rcases hz with h | h | h | h | h
  · rw [h]; exact hLψ
  · rw [h]; exact hRψ
  · rw [h]; exact hDψ
  · rw [h]; exact hNψ
  · rw [h]; exact hCψ

/-- The finite central discs can be frozen at a real-type source potential.
On one open neighborhood, every nearby indexed cluster stays in its
base-point disc, and distinct discs are disjoint. -/
theorem exists_local_sourceClusterDiscs_finite_block
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (s : Finset ℤ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      (∀ ψ ∈ U, ∀ n ∈ s,
        sourceSpectralCluster hp hp1 ψ n ⊆ sourceClusterDisc hp hp1 φ (fun _ => ε) n) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j →
        Disjoint (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
          (sourceClusterDisc hp hp1 φ (fun _ => ε) j)) := by
  obtain ⟨ε, hε, hbase, hdisjoint⟩ := exists_sourceClusterDiscs_finite_block hp hp1 φ hφ s
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ n ∈ s,
      sourceSpectralCluster hp hp1 ψ n ⊆ sourceClusterDisc hp hp1 φ (fun _ => ε) n := by
    rw [Finset.eventually_all]
    intro n hn
    exact eventually_sourceSpectralCluster_subset_open hp hp1 φ hφ n _
      Metric.isOpen_ball (hbase n hn)
  obtain ⟨U, hUsub, hUopen, hφU⟩ := _root_.mem_nhds_iff.mp hevent
  exact ⟨ε, hε, U, hUopen, hφU,
    (fun ψ hψ => hUsub hψ), hdisjoint⟩

/-- The locally persistent finite central discs may use one shared margin
below any prescribed positive bound. -/
theorem exists_local_sourceClusterDiscs_finite_block_bounded
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (s : Finset ℤ) {B : ℝ} (hB : 0 < B) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ B ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
        (∀ ψ ∈ U, ∀ n ∈ s,
          sourceSpectralCluster hp hp1 ψ n ⊆ sourceClusterDisc hp hp1 φ (fun _ => ε) n) ∧
        (∀ i ∈ s, ∀ j ∈ s, i < j →
          Disjoint (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
            (sourceClusterDisc hp hp1 φ (fun _ => ε) j)) := by
  obtain ⟨ε, hε, hεB, hbase, hdisjoint⟩ :=
    exists_sourceClusterDiscs_finite_block_bounded hp hp1 φ hφ s hB
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ n ∈ s,
      sourceSpectralCluster hp hp1 ψ n ⊆ sourceClusterDisc hp hp1 φ (fun _ => ε) n := by
    rw [Finset.eventually_all]
    intro n hn
    exact eventually_sourceSpectralCluster_subset_open hp hp1 φ hφ n _
      Metric.isOpen_ball (hbase n hn)
  obtain ⟨U, hUsub, hUopen, hφU⟩ := _root_.mem_nhds_iff.mp hevent
  exact ⟨ε, hε, hεB, U, hUopen, hφU,
    (fun ψ hψ => hUsub hψ), hdisjoint⟩

end NLS.ZakharovShabat
