import NLS.KdV.HillWeightedColumnIndexRatios
import NLS.ZakharovShabat.SourcePsiGapIndexRatioUniformTail
import NLS.ZakharovShabat.SourcePsiQuotientUniformGapProductTail
import NLS.ComplexAnalysis.FourFactorNearOne

/-! The regular weighted diagonal column tends to minus one on actual
high gaps UNIFORMLY before all numerator indices and balanced full gap
inputs. The original complex quotient and all near-neighbor indices are
retained; no uniformity is inferred from bounded sequence norms alone. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillWeightedColumnGapNumerator_uniform_gap_tail
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax 2 ψ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ c : ℂ, ∀ d : lp (fun _ : ℕ+ => ℂ) 2,
      hillIndependentFrequencyDisplacement (c,d) ∈ sourcePeriodicGapRootSet (by norm_num) (by norm_num) ψ →
      ∀ n m : ℕ+, N ≤ (m:ℕ) → m ≠ n →
        ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ),
          ‖hillPeriodEquationWeight n m*hillProductColumnGapNumerator n m c ψ ((m:ℕ):ℤ) d z+1‖ < ε := by
  obtain ⟨η,hη,hfour⟩ := exists_fourFactor_tolerance ε hε
  obtain ⟨NR,hR⟩ := hD.gap_indexRatio_uniform_tail ψ hψ η hη
  obtain ⟨δ,hδ,NQ,hQ⟩ := exists_sourcePsiQuotient_uniformSmallTail_near_gapProduct
    (by norm_num) (by norm_num) (⟨ψ,hreal⟩:realTypeSourceLocus 2) η hη
  refine ⟨max NR NQ,?_⟩
  intro c d ha n m hm hmn z hz
  let a := hillIndependentFrequencyDisplacement (c,d)
  have hmR : NR ≤ (((m:ℕ):ℤ)).natAbs := by simpa only [Int.natAbs_natCast] using (le_max_left NR NQ).trans hm
  have hmQ : NQ ≤ (((m:ℕ):ℤ)).natAbs := by simpa only [Int.natAbs_natCast] using (le_max_right NR NQ).trans hm
  have hmn' : ((n:ℕ):ℤ) ≠ ((m:ℕ):ℤ) := by intro h; exact hmn (Subtype.ext (Int.ofNat.inj h.symm))
  have hmneg : -((m:ℕ):ℤ) ≠ ((m:ℕ):ℤ) := by have := m.pos; omega
  have hnneg : -((n:ℕ):ℤ) ≠ ((m:ℕ):ℤ) := by have := n.pos; have := m.pos; omega
  have hplace (k : ℤ) : hillIndependentFrequency (c,d) k ∈ D k := hD.gap ψ hψ k (ha k)
  have hother : z ∈ sourceStandardRootOmittedDomain (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) := by
    intro k hkm hzk
    exact Set.disjoint_left.mp (hD.disjoint ((m:ℕ):ℤ) k hkm.symm) (hD.gap ψ hψ _ hz) (hD.gap ψ hψ k hzk)
  have ht : (a,ψ) ∈ cthickening δ (sourcePeriodicGapRootSet (by norm_num) (by norm_num) ψ ×ˢ {ψ}) :=
    mem_cthickening_of_dist_le (a,ψ) (a,ψ) δ _ ⟨ha,mem_singleton ψ⟩ (by simpa only [dist_self] using hδ.le)
  have hq := hQ (a,ψ) ht ((m:ℕ):ℤ) hmQ
  have hqz := hq.2 z (ball_subset_closedBall (hq.1 hz))
  have hb := hfour
    (sourcePsiOriginalIndexRatio (-((m:ℕ):ℤ)) ((m:ℕ):ℤ) a z)
    (sourcePsiOriginalIndexRatio ((n:ℕ):ℤ) ((m:ℕ):ℤ) a z)
    (sourcePsiOriginalIndexRatio (-((n:ℕ):ℤ)) ((m:ℕ):ℤ) a z)
    (sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ) (z,(a,ψ)))
    (hR _ hmR a ha _ hmneg z hz) (hR _ hmR a ha _ hmn' z hz) (hR _ hmR a ha _ hnneg z hz) hqz
  rw [hillWeightedColumnGapNumerator_eq_indexRatios hD ψ c d hplace n m hmn z
    (subset_closure (hD.gap ψ hψ _ hz)) hother]
  have he (A B E Q : ℂ) : -A*B*E*Q+1 = -(A*B*E*Q-1) := by ring
  rw [he,norm_neg]
  exact hb

end NLS.KdV
