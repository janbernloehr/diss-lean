import NLS.ZakharovShabat.SourceCriticalHalfGapBounds

/-! # Lemma F.1: critical-point bounds relative to the periodic gap

Part (i) applies at every collapsed complex point of a single connected
almost-real domain. Part (ii) supplies one complex neighborhood for all
signed indices around each real source, including collapsed head gaps.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceCriticalGapAnalyticDomain
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (D : SourceCriticalGapAnalyticDomain hp hp1)

/-- F.1(i), with the printed half-gap constant and no real-type assumption on the base point. -/
theorem sourceLemmaF1_i (φ : CoeffPair p) (hφ : φ ∈ D.domain) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ D.domain ∧ ∀ ψ ∈ V,
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
          ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖/2 := by
  simpa only [sourcePeriodicGapDisplacement_apply,one_div,mul_comm (2:ℝ)⁻¹,← div_eq_mul_inv] using
    D.exists_collapsedGap_bound φ hφ n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap) (1/2) (by norm_num)

/-- F.1(ii): one neighborhood works for every signed index, with the printed constant one. -/
theorem sourceLemmaF1_ii (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ D.domain ∧ ∀ ψ ∈ V, ∀ n : ℤ,
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
          ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ := by
  have hφD := D.real_subset hφ
  obtain ⟨N,U,hU,hφU,htail⟩ := exists_local_sourceCriticalOffset_small_gap_tail hp hp1 φ hφ 1 (by norm_num)
  have hhead : ∀ᶠ ψ in 𝓝 φ, ∀ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
          ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
    rw [Finset.eventually_all]
    intro n _
    by_cases hg : sourcePeriodicGapDisplacement hp hp1 φ n = 0
    · obtain ⟨V,hV,hφV,_,hbound⟩ := D.exists_collapsedGap_bound φ hφD n hg 1 (by norm_num)
      filter_upwards [hV.mem_nhds hφV] with ψ hψ
      simpa only [one_mul] using hbound ψ hψ
    · have hhalf := norm_sourceCriticalPoint_sub_midpoint_le_halfGap_of_realType hp hp1 φ hφ n
      have hpos := norm_pos_iff.mpr hg
      have hlt : ‖canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n-
          canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ <
            ‖sourcePeriodicGapDisplacement hp hp1 φ n‖ := by linarith
      exact ((D.analyticAt_offset φ hφD n).continuousAt.norm.eventually_lt
        (D.continuousAt_gap_norm φ hφD n) hlt).mono (fun _ h => h.le)
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp
    (hhead.and (Filter.Eventually.and (hU.mem_nhds hφU) (D.isOpen.mem_nhds hφD)))
  refine ⟨V,hV,hφV,fun ψ hψ => (hVsub hψ).2.2,?_⟩
  intro ψ hψ n
  by_cases hn : n.natAbs ≤ N
  · have hi : n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by simp only [Finset.mem_Icc]; omega
    simpa only [sourcePeriodicGapDisplacement_apply] using (hVsub hψ).1 n hi
  · simpa only [one_mul,sourcePeriodicGapDisplacement_apply] using
      htail ψ (hVsub hψ).2.1 n (by omega)

end SourceCriticalGapAnalyticDomain

/-- Both parts of F.1 hold on one constructed almost-real domain, with their literal constants. -/
theorem sourceLemmaF1 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      (∀ φ ∈ W, ∀ n : ℤ,
        canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0 →
        ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧ ∀ ψ ∈ V,
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
            canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
              ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖/2) ∧
      (∀ φ : CoeffPair p, IsRealType (CoeffPair.toMax p φ) →
        ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧ ∀ ψ ∈ V, ∀ n : ℤ,
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
            canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
              ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖) := by
  obtain ⟨D⟩ := nonempty_sourceCriticalGapAnalyticDomain hp hp1
  exact ⟨D.domain,D.isOpen,D.isConnected,D.real_subset,D.sourceLemmaF1_i,D.sourceLemmaF1_ii⟩

end NLS.ZakharovShabat
