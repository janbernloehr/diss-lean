import NLS.KdV.HillHminusOneLowNormalizedActions

/-! # One neighborhood for every nonzero normalized canonical action

First choose the uniform high cutoff. Only FINITELY many remaining low
indices require their own neighborhoods; their finite intersection gives
ONE real-centered complex ball supporting ALL analytic nonzero ratios.
The union of these balls is open, connected and contains the entire real
H-minus-one form. Action and squared-gap zero sets agree there at ALL
positive indices, including complex collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.KdV

structure HillHminusNormalizedActionBall where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset_gap : ball center radius ⊆ hillHminusCanonicalGapDomain
  ratio : ℕ+ → PeriodOneHminusOne → ℂ
  ratio_analytic : ∀ n, AnalyticOnNhd ℂ (ratio n) (ball center radius)
  ratio_nonzero : ∀ n, ∀ a ∈ ball center radius, ratio n a ≠ 0
  factor : ∀ n, ∀ a ∈ ball center radius,
    hillHminusCanonicalAction n a = hillHminusCanonicalGapSquare n a /
      (8*((Real.pi : ℂ)*(n : ℕ)))*ratio n a

namespace HillHminusNormalizedActionBall

def source (B : HillHminusNormalizedActionBall) : Set PeriodOneHminusOne := ball B.center B.radius

theorem source_open (B : HillHminusNormalizedActionBall) : IsOpen B.source := isOpen_ball

theorem action_eq_zero_iff_gapSquare (B : HillHminusNormalizedActionBall) (n : ℕ+)
    (a : PeriodOneHminusOne) (ha : a ∈ B.source) :
    hillHminusCanonicalAction n a = 0 ↔ hillHminusCanonicalGapSquare n a = 0 := by
  have hK : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  rw [B.factor n a ha]
  simp only [mul_eq_zero,div_eq_zero_iff,B.ratio_nonzero n a ha,hK,or_false]

end HillHminusNormalizedActionBall

theorem exists_hillHminusNormalizedActionBall
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusNormalizedActionBall, q ∈ B.source := by
  obtain ⟨N,T,_,hT,hqT,hTgap,hhigh⟩ :=
    exists_hillHminus_canonical_gap_high_normalization_at_complex q
      (real_mem_hillHminusCanonicalGapDomain q hq) 1 (by norm_num)
  have hlow := fun n : ℕ+ => exists_local_hillHminus_canonical_normalized_ratio q hq n
  choose V hV hqV hVgap R hR hdata using hlow
  have hfinite : ∀ᶠ a in 𝓝 q, ∀ k ∈ Finset.range N, ∀ hk : 0 < k, a ∈ V ⟨k,hk⟩ := by
    rw [Finset.eventually_all]
    intro k _
    by_cases hk : 0 < k
    · filter_upwards [(hV ⟨k,hk⟩).mem_nhds (hqV ⟨k,hk⟩)] with a ha
      intro _
      exact ha
    · exact Filter.Eventually.of_forall (fun _ hk' => (hk hk').elim)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hT.mem_nhds hqT) hfinite)
  let F : ℕ+ → PeriodOneHminusOne → ℂ := fun n a =>
    if N ≤ (n : ℕ) then hillHminusGluedHighActionRatio n a else R n a
  have hsmall (n : ℕ+) (hn : ¬ N ≤ (n : ℕ)) : ball q r ⊆ V n := by
    intro a ha
    exact (hball ha).2 (n : ℕ) (Finset.mem_range.mpr (lt_of_not_ge hn)) n.pos
  let B : HillHminusNormalizedActionBall := {
    center := q
    center_real := hq
    radius := r
    radius_pos := hr
    subset_gap := fun a ha => hTgap (hball ha).1
    ratio := F
    ratio_analytic := by
      intro n
      by_cases hn : N ≤ (n : ℕ)
      · simpa only [F,if_pos hn] using (hhigh n hn).1.mono (fun a ha => (hball ha).1)
      · simpa only [F,if_neg hn] using (hR n).mono (hsmall n hn)
    ratio_nonzero := by
      intro n a ha
      by_cases hn : N ≤ (n : ℕ)
      · exact (by simpa only [F,if_pos hn] using ((hhigh n hn).2 a (hball ha).1).2.1)
      · exact (by simpa only [F,if_neg hn] using (hdata n a (hsmall n hn ha)).1)
    factor := by
      intro n a ha
      by_cases hn : N ≤ (n : ℕ)
      · exact (by simpa only [F,if_pos hn] using ((hhigh n hn).2 a (hball ha).1).2.2.1)
      · exact (by simpa only [F,if_neg hn] using (hdata n a (hsmall n hn ha)).2.1) }
  exact ⟨B,mem_ball_self hr⟩

def hillHminusCanonicalRatioDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusNormalizedActionBall, B.source

theorem isOpen_hillHminusCanonicalRatioDomain : IsOpen hillHminusCanonicalRatioDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusCanonicalRatioDomain_subset : hillHminusCanonicalRatioDomain ⊆ hillHminusCanonicalGapDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset_gap hB

theorem real_mem_hillHminusCanonicalRatioDomain (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : q ∈ hillHminusCanonicalRatioDomain := by
  obtain ⟨B,hB⟩ := exists_hillHminusNormalizedActionBall q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusCanonicalRatioDomain : IsConnected hillHminusCanonicalRatioDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusNormalizedActionBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusNormalizedActionBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusNormalizedActionBall, S ∪ B.source) = hillHminusCanonicalRatioDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusCanonicalRatioDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusCanonicalRatioDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

theorem hillHminusCanonicalAction_eq_zero_iff_gapSquare
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalRatioDomain) :
    hillHminusCanonicalAction n q = 0 ↔ hillHminusCanonicalGapSquare n q = 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.action_eq_zero_iff_gapSquare n q hB

end NLS.KdV
