import NLS.ZakharovShabat.SourceStandardRootNorm

/-!
# Equation (2.10) for two distant isolating discs

The fixed free quarter-π discs have linear pointwise separation in their
signed indices. The standard-root norm identity transfers that separation
to every source potential in a common local neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Equation (2.10) with explicit constants for two distinct tail discs. -/
theorem sourceStandardRoot_tail_disc_norm_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) {m n : ℤ} (hmn : m ≠ n)
    (hm : ¬ m.natAbs ≤ N) (hn : ¬ n.natAbs ≤ N)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    {z : ℂ} (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε m) :
    (Real.pi/2)*|((m-n : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ ∧
      ‖sourceStandardRoot hp hp1 ψ n z‖ ≤
        (3*Real.pi/2)*|((m-n : ℤ) : ℝ)| := by
  have hz' : z ∈ refinedResonantDisk m := by
    simpa only [sourceIsolatingDisc, if_neg hm] using hz
  have hL' : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ∈ refinedResonantDisk n := by
    simpa only [sourceIsolatingDisc, if_neg hn] using hcluster (Or.inl rfl)
  have hR' : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ∈ refinedResonantDisk n := by
    simpa only [sourceIsolatingDisc, if_neg hn] using hcluster (Or.inr (Or.inl rfl))
  have hL := refinedResonantDisk_pointwise_separation hmn hz' hL'
  have hR := refinedResonantDisk_pointwise_separation hmn hz' hR'
  have hdisjoint : Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n) := by
    simpa only [sourceIsolatingDisc, if_neg hm, if_neg hn] using
      refinedResonantDisk_disjoint hmn
  have hsegment := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε n hcluster
  have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    intro hzin
    exact (Set.disjoint_left.mp hdisjoint hz) (hsegment hzin)
  apply sourceStandardRoot_norm_bounds_of_endpoint_bounds hp hp1 ψ n z hznot
    ((Real.pi/2)*|((m-n : ℤ) : ℝ)|)
    ((3*Real.pi/2)*|((m-n : ℤ) : ℝ)|)
    (by positivity) (by positivity)
  · simpa only [dist_eq_norm, norm_sub_rev] using hL.1
  · simpa only [dist_eq_norm, norm_sub_rev] using hR.1
  · simpa only [dist_eq_norm, norm_sub_rev] using hL.2
  · simpa only [dist_eq_norm, norm_sub_rev] using hR.2

/-- One connected source neighborhood gives the same explicit tail-disc
root bounds at every nearby potential and all distant signed indices. -/
theorem exists_local_source_tail_standardRoot_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∀ ψ ∈ V, ∀ m n : ℤ, m ≠ n → N < m.natAbs → N < n.natAbs →
          ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε m,
            (Real.pi/2)*|((m-n : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ ∧
              ‖sourceStandardRoot hp hp1 ψ n z‖ ≤
                (3*Real.pi/2)*|((m-n : ℤ) : ℝ)| := by
  obtain ⟨N, ε, hε, _, V, hVopen, hVconnected, hφV, hcluster, _⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  refine ⟨N, ε, hε, V, hVopen, hVconnected, hφV, ?_⟩
  intro ψ hψ m n hmn hm hn z hz
  exact sourceStandardRoot_tail_disc_norm_bounds hp hp1 φ ψ N ε hmn
    (not_le.mpr hm) (not_le.mpr hn) (hcluster ψ hψ n) hz

end NLS.ZakharovShabat
