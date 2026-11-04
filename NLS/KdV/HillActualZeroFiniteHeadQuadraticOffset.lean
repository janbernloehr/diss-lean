import NLS.KdV.HillBalancedQuadraticOffset
import NLS.KdV.HillSourceMidpointGapContinuity
import NLS.ZakharovShabat.SourcePsiCollapsedGapOffsetGeometry

/-! Every fixed original row has one quadratic frequency-gap bound
BEFORE ALL numerator indices. A collapsed reference gap uses a genuine
fixed small contour; a noncollapsed gap stays bounded away from zero.
Finite intersection and summation give a common finite-head estimate. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_fixed_row_actual_zero_quadratic_frequency_offset (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+, m ≠ n →
        ‖hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),hillHminusCanonicalZeroSequence n y) ((m:ℕ):ℤ)-
          sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ ≤
            L*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖^2 := by
  let k : ℤ := ((m:ℕ):ℤ)
  let γ : PeriodOneHminusOne → ℂ := fun y => sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) k
  let τ : PeriodOneHminusOne → ℂ := fun y => sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) k
  have hγcont : ContinuousAt γ q := P.continuousAt_source_frequency_gap q hq hr k
  have hτcont : ContinuousAt τ q := P.continuousAt_source_frequency_midpoint q hq hr k
  obtain ⟨rP,hrP,hU,hperiod⟩ := P.exists_common_canonical_zero_sequence_period_ball q hq hr
  have hC : 0 < P.separation := zero_lt_one.trans_le P.isolating.one_le
  by_cases hγ : γ q = 0
  · obtain ⟨rQ,Q,hrQ,hQ,_,hupper⟩ := P.exists_common_zero_sequence_allDisc_quotient_upper_bound q hq hr
    obtain ⟨rL,c₀,hrL,hc₀,_,hlower⟩ := P.exists_common_zero_sequence_midpoint_quotient_lower_bound q hq hr
    have hmid : τ q ∈ P.discs k := P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k
      (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) k)
    have hopen : IsOpen (P.discs k) := by rw [P.discs_eq]; exact isOpen_ball
    obtain ⟨δ,hδ,hδball⟩ := Metric.isOpen_iff.mp hopen (τ q) hmid
    let R := δ/2
    have hR : 0 < R := half_pos hδ
    have hball : closedBall (τ q) R ⊆ P.discs k :=
      (closedBall_subset_ball (by dsimp only [R]; linarith)).trans hδball
    have hmidnear : ∀ᶠ y in 𝓝 q, ‖τ y-τ q‖ < R/4 := by
      simpa only [mem_ball,dist_eq_norm] using hτcont.eventually (ball_mem_nhds (τ q) (by positivity : 0 < R/4))
    have hgapnear : ∀ᶠ y in 𝓝 q, ‖γ y‖ < R/2 := by
      have h := hγcont.eventually (ball_mem_nhds (γ q) (by positivity : 0 < R/2))
      simpa only [hγ,mem_ball,dist_zero_right] using h
    obtain ⟨rG,hrG,hG⟩ := Metric.mem_nhds_iff.mp (hmidnear.and hgapnear)
    let r := min rP (min rQ (min rL rG))
    have hrpos : 0 < r := lt_min hrP (lt_min hrQ (lt_min hrL hrG))
    have hrp : r ≤ rP := min_le_left _ _
    have hrq : r ≤ rQ := (min_le_right _ _).trans (min_le_left _ _)
    have hrl : r ≤ rL := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hrg : r ≤ rG := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    let L := (R*(2*P.separation)/(2*(R/2)^3*c₀))*(2*(1+2*P.separation/P.separation⁻¹)^2*Q)
    refine ⟨r,L,hrpos,by dsimp only [L]; positivity,(ball_subset_ball hrp).trans hU,?_⟩
    intro y hy n hmn
    obtain ⟨hm,hg⟩ := hG (ball_subset_ball hrg hy)
    have hseg := sourcePeriodicSegment_subset_ball_of_small_midpoint_gap (by norm_num) (by norm_num)
      (P.sourcePsi y) k (τ q) R hR hm.le hg.le
    have hsep (z : ℂ) (hz : z ∈ sphere (τ q) R) : R/2 ≤ ‖τ y-z‖ := by
      have hzdist : ‖z-τ q‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hz
      have htri : ‖z-τ q‖ ≤ ‖z-τ y‖+‖τ y-τ q‖ := by
        calc
          _ = ‖(z-τ y)+(τ y-τ q)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      rw [norm_sub_rev z (τ y)] at htri
      linarith
    have hper := hperiod y (ball_subset_ball hrp hy) n
    exact P.norm_balanced_zero_sequence_frequency_offset_le n m hmn y (hillHminusCanonicalZeroSequence n y)
      hper.1 hper.2 (τ q) R (R/2) Q c₀ hR (half_pos hR) hQ hc₀ hseg hball hsep hg.le
      (fun z hz => hupper y (ball_subset_ball hrq hy) n k z hz) (hlower y (ball_subset_ball hrl hy) n k)
  · let g := ‖γ q‖/2
    have hg : 0 < g := half_pos (norm_pos_iff.mpr hγ)
    have hgapnear : ∀ᶠ y in 𝓝 q, g < ‖γ y‖ :=
      hγcont.norm.eventually (Ioi_mem_nhds (by dsimp only [g]; linarith [norm_pos_iff.mpr hγ]))
    obtain ⟨rG,hrG,hG⟩ := Metric.mem_nhds_iff.mp hgapnear
    let L := (2*P.separation)/g^2
    have hL : 0 ≤ L := by dsimp only [L]; positivity
    refine ⟨min rP rG,L,lt_min hrP hrG,hL,(ball_subset_ball (min_le_left _ _)).trans hU,?_⟩
    intro y hy n _
    have hper := hperiod y (ball_subset_ball (min_le_left _ _) hy) n
    have hplace := hper.1.1.2 k
    have hmid := P.isolating.gap (P.sourcePsi y) (P.image y hper.1.2).2 k
      (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi y) k)
    have hcoarse := P.isolating.uniform_disc_diameter k _ _ hplace hmid
    have hgl : g ≤ ‖γ y‖ := (hG (ball_subset_ball (min_le_right _ _) hy)).le
    have hsq : g^2 ≤ ‖γ y‖^2 := pow_le_pow_left₀ hg.le hgl 2
    calc
      _ ≤ 2*P.separation := hcoarse
      _ = L*g^2 := by dsimp only [L]; field_simp
      _ ≤ L*‖γ y‖^2 := mul_le_mul_of_nonneg_left hsq hL

theorem exists_finite_head_actual_zero_quadratic_frequency_offset (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (s : Finset ℕ+) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ y ∈ ball q r, ∀ n m : ℕ+, m ∈ s → m ≠ n →
        ‖hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),hillHminusCanonicalZeroSequence n y) ((m:ℕ):ℤ)-
          sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ ≤
            L*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖^2 := by
  choose r L hrpos hL _ hb using fun m : ℕ+ => P.exists_fixed_row_actual_zero_quadratic_frequency_offset q hq hr m
  let U := ⋂ m ∈ s, ball q (r m)
  have hU : IsOpen U := isOpen_biInter_finset (fun m _ => isOpen_ball)
  have hqU : q ∈ U := mem_iInter₂.mpr (fun m _ => mem_ball_self (hrpos m))
  obtain ⟨ρ,hρ,hρU⟩ := Metric.isOpen_iff.mp hU q hqU
  refine ⟨ρ,∑ m ∈ s,L m,hρ,Finset.sum_nonneg (fun m _ => hL m),?_⟩
  intro y hy n m hm hmn
  have hym : y ∈ ball q (r m) := mem_iInter₂.mp (hρU hy) m hm
  exact (hb m y hym n hmn).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun m _ => hL m) hm) (sq_nonneg _))

end NLS.KdV.HillProductEquationPatch
