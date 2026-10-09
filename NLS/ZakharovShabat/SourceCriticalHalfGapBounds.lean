import NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain
import NLS.ZakharovShabat.SourceAbelianMomentSquaredOffsetError

/-! # Half-gap estimates near collapsed complex gaps

The squared-gap identity makes the ratio to gap magnitude tend to zero
at a collapsed gap, without division by that gap or analytic endpoint
branches. A separate tail argument is uniform in the spectral index.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceCriticalGapAnalyticDomain
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (D : SourceCriticalGapAnalyticDomain hp hp1)

/-- At every collapsed complex gap, any positive linear gap constant works locally. -/
theorem exists_collapsedGap_bound (φ : CoeffPair p) (hφ : φ ∈ D.domain) (n : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ D.domain ∧ ∀ ψ ∈ V,
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
          ε*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  have hc := (D.continuousAt_gap_norm φ hφ n).mul (D.quotient_analytic n φ hφ).continuousAt.norm
  have hlt : ‖sourcePeriodicGapDisplacement hp hp1 φ n‖*
      ‖sourceCriticalGapQuotient hp hp1 φ n‖ < ε := by rw [hgap,norm_zero,zero_mul]; exact hε
  have hnear : ∀ᶠ ψ in 𝓝 φ, ψ ∈ D.domain ∧
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*‖sourceCriticalGapQuotient hp hp1 ψ n‖ < ε := by
    filter_upwards [D.isOpen.mem_nhds hφ,hc.eventually (gt_mem_nhds hlt)] with ψ hψ hbound
    exact ⟨hψ,hbound⟩
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨V,hV,hφV,fun ψ hψ => (hVsub hψ).1,?_⟩
  intro ψ hψ
  rw [D.offset_eq ψ (hVsub hψ).1 n,norm_mul,norm_pow]
  have h := mul_le_mul_of_nonneg_left (hVsub hψ).2.le
    (norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n))
  nlinarith

end SourceCriticalGapAnalyticDomain

/-- Real interlacing puts the critical point within half the gap of its midpoint. -/
theorem norm_sourceCriticalPoint_sub_midpoint_le_halfGap_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ‖canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 φ n‖/2 := by
  have h := norm_sourceMidpoint_sub_le_halfGap hp hp1 φ n _
    (sourceCanonicalCriticalPoint_mem_periodicSegment_of_realType hp hp1 n φ hφ)
  simpa only [sourceStandardRootMidpoint,norm_sub_rev] using h

/-- The critical offset is an arbitrarily small multiple of the gap on a common tail neighborhood. -/
theorem exists_local_sourceCriticalOffset_small_gap_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∀ ψ ∈ V,
      ∀ n : ℤ, N < n.natAbs →
        ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
          canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
            ε*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  obtain ⟨U,hU,hφU,K,hK,hq⟩ := exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  let δ := ε/(K+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ*K ≤ ε := by
    have hid : δ*(K+1) = ε := by dsimp [δ]; field_simp
    nlinarith
  obtain ⟨N,_,V,hV,hφV,_,_,hg⟩ := exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ hδ
  refine ⟨N,U ∩ V,hU.inter hV,⟨hφU,hφV⟩,?_⟩
  intro ψ hψ n hn
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hqn : ‖sourceCriticalGapQuotient hp hp1 ψ n‖ ≤ K :=
    (lp.norm_apply_le_norm hp0 _ n).trans (hq ψ hψ.1).1
  have hgn : ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ ≤ δ := by
    have ht := (lp.norm_apply_le_norm hp0
      (sourcePeriodicGapDisplacement hp hp1 ψ-
        Coeff.truncate (Finset.Icc (-(N:ℤ)) (N:ℤ)) (sourcePeriodicGapDisplacement hp hp1 ψ)) n).trans
          ((hg ψ hψ.2).2 N le_rfl)
    have hnS : n ∉ Finset.Icc (-(N:ℤ)) (N:ℤ) := by simp only [Finset.mem_Icc]; omega
    simpa only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,if_neg hnS,sub_zero] using ht
  rw [(hq ψ hψ.1).2 n,norm_mul,norm_pow]
  have hprod := (mul_le_mul hgn hqn (norm_nonneg _) hδ.le).trans hδε
  have h := mul_le_mul_of_nonneg_left hprod (norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n))
  nlinarith

end NLS.ZakharovShabat
