import NLS.ZakharovShabat.SourceCriticalRootRatioUniformTailBound

/-! # Uniform linear gap bounds for the regular numerator

The exact squared-gap critical offset and a local gap norm bound control
the distance from the critical point to every point of its complex gap.
The uniformly bounded deleted factor then gives a numerator bound linear
in the actual gap length, including a collapsed gap.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem midpoint_sub_norm_le_two_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ n) :
    ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ ≤
      2*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hsub : sourcePeriodicSegment hp hp1 ψ n ⊆ closedBall l ‖r-l‖ :=
    (convex_closedBall l ‖r-l‖).segment_subset (mem_closedBall_self (norm_nonneg _))
      (by rw [mem_closedBall,dist_eq_norm])
  have hm := mem_closedBall.mp (hsub (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))
  have hz' := mem_closedBall.mp (hsub hz)
  rw [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
  change _ ≤ 2*‖r-l‖
  rw [← dist_eq_norm]
  calc
    _ ≤ dist (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) l+dist l z := dist_triangle _ _ _
    _ ≤ ‖r-l‖+‖r-l‖ := add_le_add hm (by simpa only [dist_comm] using hz')
    _ = 2*‖r-l‖ := by ring

/-- The critical point is at most a uniform multiple of the gap length
from any point of that gap, for nearby complex sources and all indices. -/
theorem exists_local_uniform_sourceCriticalPoint_gap_distance_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ B : ℝ, 0 < B ∧
      ∀ ψ ∈ V, ∀ n : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
        ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z‖ ≤
          B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  obtain ⟨Vq,hVq,hφq,K,hK,hq⟩ := exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hg⟩ := exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  refine ⟨Vq ∩ Vg,hVq.inter hVg,⟨hφq,hφg⟩,G*K+2,by positivity,?_⟩
  intro ψ hψ n z hz
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hgn : ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ ≤ G :=
    (lp.norm_apply_le_norm hp0 _ n).trans (hg ψ hψ.2).1
  have hqn : ‖sourceCriticalGapQuotient hp hp1 ψ n‖ ≤ K :=
    (lp.norm_apply_le_norm hp0 _ n).trans (hq ψ hψ.1).1
  have hmid := midpoint_sub_norm_le_two_gap hp hp1 ψ n z hz
  have hd := norm_sub_le_norm_sub_add_norm_sub
    (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) z
  rw [(hq ψ hψ.1).2 n,norm_mul,norm_pow] at hd
  have hprod : ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2*‖sourceCriticalGapQuotient hp hp1 ψ n‖ ≤
      (G*K)*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
    have h₁ := mul_le_mul_of_nonneg_left hqn (sq_nonneg ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖)
    have h₂ := mul_le_mul_of_nonneg_right hgn (mul_nonneg hK (norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n)))
    nlinarith
  nlinarith

/-- One constant bounds the regular numerator on every distant closed
complex gap by that gap's length, uniformly in the source. -/
theorem exists_local_uniform_sourceCriticalRootGapNumerator_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs → ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
        ‖sourceCriticalRootGapNumerator hp hp1 ψ n z‖ ≤ B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  obtain ⟨Ve,hVe,hφe,Ke,M,hM,he⟩ := exists_local_uniform_sourceCriticalRootRatioExtension_tail_bound hp hp1 φ hφ
  obtain ⟨Vd,hVd,hφd,A,hA,hd⟩ := exists_local_uniform_sourceCriticalPoint_gap_distance_bound hp hp1 φ hφ
  obtain ⟨N,ε,_,_,Vg,hVg,_,hφg,hcluster,_⟩ := exists_local_source_connected_isolating_discs hp hp1 φ hφ
  refine ⟨(Ve ∩ Vd) ∩ Vg,(hVe.inter hVd).inter hVg,⟨⟨hφe,hφd⟩,hφg⟩,max Ke (N+1),A*M,mul_pos hA hM,?_⟩
  intro ψ hψ n hn z hz
  have hzn := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε n (hcluster ψ hψ.2 n) hz
  have hnN : ¬n.natAbs ≤ N := by omega
  have hzB : z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) := by
    simpa only [sourceIsolatingDisc,if_neg hnN,refinedResonantDisk] using hzn
  have hnE : Ke ≤ n.natAbs := by omega
  have hb := mul_le_mul (hd ψ hψ.1.2 n z hz) (he ψ hψ.1.1 n hnE z hzB)
    (norm_nonneg _) (mul_nonneg hA.le (norm_nonneg _))
  simpa only [sourceCriticalRootGapNumerator,norm_mul,mul_assoc,mul_comm,mul_left_comm] using hb

end NLS.ZakharovShabat
