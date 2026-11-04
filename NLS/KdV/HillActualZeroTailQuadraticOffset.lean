import NLS.KdV.HillBalancedQuadraticOffset
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles

/-! The ACTUAL common complex Hill zero sequences have one quadratic
frequency-gap offset bound BEFORE ALL numerator indices and ALL tail
rows. Every contour is the genuine fixed eighth-pi circle inside the
ORIGINAL assigned disc; low and collapsed gaps are not excluded from
the preceding general offset theorem. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_common_actual_zero_tail_quadratic_frequency_offset (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∃ K : ℕ, ∀ y ∈ ball q r, ∀ n m : ℕ+, K ≤ (m:ℕ) → m ≠ n →
        ‖hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),hillHminusCanonicalZeroSequence n y) ((m:ℕ):ℤ)-
          sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ ≤
            L*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖^2 := by
  obtain ⟨rP,hrP,hU,hperiod⟩ := P.exists_common_canonical_zero_sequence_period_ball q hq hr
  obtain ⟨rQ,Q,hrQ,hQ,_,hupper⟩ := P.exists_common_zero_sequence_allDisc_quotient_upper_bound q hq hr
  obtain ⟨rL,c₀,hrL,hc₀,_,hlower⟩ := P.exists_common_zero_sequence_midpoint_quotient_lower_bound q hq hr
  obtain ⟨Kt,V,hV,hbase,htiny⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (P.sourcePsi q)
  have hO : IsOpen (P.source ∩ P.sourcePsi ⁻¹' V) :=
    P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hV
  obtain ⟨rT,hrT,hT⟩ := Metric.isOpen_iff.mp hO q ⟨hq,hbase⟩
  obtain ⟨N,htail⟩ := P.isolating.tail
  let r := min rP (min rQ (min rL rT))
  have hrpos : 0 < r := lt_min hrP (lt_min hrQ (lt_min hrL hrT))
  have hrp : r ≤ rP := min_le_left _ _
  have hrq : r ≤ rQ := (min_le_right _ _).trans (min_le_left _ _)
  have hrl : r ≤ rL := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrt : r ≤ rT := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  let L := ((Real.pi/8)*(2*P.separation)/(2*(Real.pi/16)^3*c₀))*(2*(1+2*P.separation/P.separation⁻¹)^2*Q)
  have hL : 0 ≤ L := by have := P.isolating.one_le; dsimp only [L]; positivity
  let K := max Kt (N+1)
  refine ⟨r,L,hrpos,hL,(ball_subset_ball hrp).trans hU,K,?_⟩
  intro y hy n m hm hmn
  let k : ℤ := ((m:ℕ):ℤ)
  let a : ℂ := (Real.pi:ℂ)*k
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) k
  have hmKt : Kt ≤ k.natAbs := by simp only [k,Int.natAbs_natCast]; dsimp only [K] at hm; omega
  have hmN : N < k.natAbs := by simp only [k,Int.natAbs_natCast]; dsimp only [K] at hm; omega
  obtain ⟨hmid,hgap⟩ := htiny (P.sourcePsi y) (hT (ball_subset_ball hrt hy)).2 k hmKt
  have hseg := sourcePeriodicSegment_subset_free_eighth_ball (by norm_num) (by norm_num) (P.sourcePsi y) k hmid hgap
  have hdisc : P.discs k = ball a (Real.pi/4) := by simpa only [a,refinedResonantDisk] using htail k hmN
  have hball : closedBall a (Real.pi/8) ⊆ P.discs k := by
    rw [hdisc]
    exact closedBall_subset_ball (by nlinarith [Real.pi_pos])
  have hsep (z : ℂ) (hz : z ∈ sphere a (Real.pi/8)) : Real.pi/16 ≤ ‖τ-z‖ := by
    have hzdist : ‖z-a‖ = Real.pi/8 := by simpa only [mem_sphere,dist_eq_norm] using hz
    have htri : ‖z-a‖ ≤ ‖z-τ‖+‖τ-a‖ := by
      calc
        _ = ‖(z-τ)+(τ-a)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev z τ] at htri
    change ‖τ-a‖ ≤ Real.pi/64 at hmid
    nlinarith [Real.pi_pos]
  have hper := hperiod y (ball_subset_ball hrp hy) n
  exact P.norm_balanced_zero_sequence_frequency_offset_le n m hmn y (hillHminusCanonicalZeroSequence n y)
    hper.1 hper.2 a (Real.pi/8) (Real.pi/16) Q c₀ (by positivity) (by positivity) hQ hc₀ hseg hball hsep
    (hgap.trans (by nlinarith [Real.pi_pos]))
    (fun z hz => hupper y (ball_subset_ball hrq hy) n k z hz) (hlower y (ball_subset_ball hrl hy) n k)

end NLS.KdV.HillProductEquationPatch
