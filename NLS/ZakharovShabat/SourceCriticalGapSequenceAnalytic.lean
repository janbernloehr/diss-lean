import NLS.ZakharovShabat.SourceDistantCriticalGapQuotientAnalyticNeighborhood
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Analyticity of the actual critical-gap quotient sequence

The common scalar analytic domain and the local sequence norm bound give
analyticity in the original coefficient norm, including collapsed gaps.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near every real source the entire actual quotient sequence is analytic. -/
theorem exists_local_sourceCriticalGapQuotient_sequence_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      AnalyticOnNhd ℂ (sourceCriticalGapQuotient hp hp1) V := by
  obtain ⟨K,U,hU,hφU,htail⟩ := exists_local_source_distantCriticalGapQuotient_analytic hp hp1 φ hφ
  have hhead : ∀ᶠ ψ in 𝓝 φ, ∀ n ∈ Finset.Icc (-(K:ℤ)) (K:ℤ),
      AnalyticAt ℂ (fun χ => sourceCriticalGapQuotient hp hp1 χ n) ψ := by
    rw [Finset.eventually_all]
    intro n _
    exact (analyticAt_sourceCriticalGapQuotient_apply_of_realType hp hp1 φ hφ n).eventually_analyticAt
  obtain ⟨H,hHsub,hH,hφH⟩ := _root_.mem_nhds_iff.mp hhead
  obtain ⟨W,hW,hφW,M,_,hb⟩ := exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  refine ⟨(U ∩ H) ∩ W,(hU.inter hH).inter hW,⟨⟨hφU,hφH⟩,hφW⟩,?_⟩
  apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ ((hU.inter hH).inter hW)
    _ M (fun ψ hψ => (hb ψ hψ.2).1)
  intro n ψ hψ
  by_cases hn : n.natAbs ≤ K
  · apply hHsub hψ.1.2 n
    simp only [Finset.mem_Icc]
    omega
  · exact htail ψ hψ.1.1 n (by omega)

end NLS.ZakharovShabat
