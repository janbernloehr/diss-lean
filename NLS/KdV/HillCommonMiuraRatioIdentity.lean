import NLS.KdV.HillMiuraNormalizedRatioLocalData
import NLS.KdV.HillHminusOneCanonicalQuotients
import NLS.ZakharovShabat.SourceHigherActionOneCommonAnalytic

/-! One native complex ball identifies EVERY sufficiently high
canonical action ratio with the SAME local Miura formula, except
for the explicit globally identically collapsed-gap convention,
where the canonical ratio is exactly one. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillHminusMiuraGapBall

private theorem canonicalRatio_eq_local_germ (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0) :
    hillHminusCanonicalActionRatio n =ᶠ[𝓝 q] B.normalizedRatio n := by
  obtain ⟨U,hU,hqU,_,ha,hfactor⟩ := B.exists_local_normalizedRatio_data n q hq hr
  have he := hillHminusCanonicalActionRatio_unique_on_open n (U ∩ hillHminusCanonicalRatioDomain)
    (hU.inter isOpen_hillHminusCanonicalRatioDomain) inter_subset_right
    (B.normalizedRatio n) (ha.mono inter_subset_left) hne (fun a ha => (hfactor a ha.1).2.1)
  filter_upwards [hU.mem_nhds hqU,isOpen_hillHminusCanonicalRatioDomain.mem_nhds
    (real_mem_hillHminusCanonicalRatioDomain q hr)] with a ha hd
  exact he ⟨ha,hd⟩

private theorem diracSum_ne_zero_of_free_circle (B : HillHminusMiuraGapBall) (q : PeriodOneHminusOne)
    (n : ℕ+)
    (hmid : sourceStandardRootMidpoint (by simp) (by norm_num) (hillMiuraDiagonal (B.actionBall.lift q)) (n:ℕ)
      ∈ ball ((Real.pi:ℂ)*(n:ℕ)) (Real.pi/8)) : B.diracSum n q ≠ 0 := by
  intro he
  have hτ : sourceStandardRootMidpoint (by simp) (by norm_num)
      (hillMiuraDiagonal (B.actionBall.lift q)) (n:ℕ) = 0 := by
    exact (mul_eq_zero.mp he).resolve_left (by norm_num : (2:ℂ) ≠ 0)
  have hb := mem_ball.mp hmid
  rw [hτ,dist_zero_left,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_natCast] at hb
  have hn : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.ne_zero
  nlinarith [Real.pi_pos]

theorem exists_local_normalizedRatio_common_analytic (B : HillHminusMiuraGapBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧
      U ⊆ B.source ∩ hillHminusCanonicalRatioDomain ∧
      ∀ n : ℕ+, N ≤ (n:ℕ) → AnalyticOnNhd ℂ (B.normalizedRatio n) U := by
  let f : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (B.actionBall.lift a)
  have hf : AnalyticOnNhd ℂ f B.source := fun a ha =>
    (hillMiuraDiagonal.analyticAt _).comp (B.actionBall.lift_analytic a ha)
  have hfreal : IsRealType (CoeffPair.toMax 2 (f q)) :=
    (hillMiuraRealSource ⟨B.actionBall.lift q,B.actionBall.lift_real q hq hr⟩).property
  obtain ⟨Na,Va,hVa,hqVa,ha⟩ :=
    exists_local_sourceHigherActionOneNormalized_common_analytic (by simp) (by norm_num) (f q) hfreal
  obtain ⟨Ng,Vg,hVg,hqVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data (by simp) (by norm_num) (f q) hfreal
  let U := (B.source ∩ f ⁻¹' (Va ∩ Vg)) ∩ hillHminusCanonicalRatioDomain
  have hU : IsOpen U :=
    (hf.continuousOn.isOpen_inter_preimage B.source_open (hVa.inter hVg)).inter isOpen_hillHminusCanonicalRatioDomain
  refine ⟨max Na Ng,U,hU,⟨⟨hq,hqVa,hqVg⟩,real_mem_hillHminusCanonicalRatioDomain q hr⟩,
    (fun a ha => ⟨ha.1.1,ha.2⟩),?_⟩
  intro n hn a haU
  have hna : Na ≤ (((n:ℕ):ℤ)).natAbs := by simpa only [Int.natAbs_natCast] using (le_max_left Na Ng).trans hn
  have hng : Ng ≤ (((n:ℕ):ℤ)).natAbs := by simpa only [Int.natAbs_natCast] using (le_max_right Na Ng).trans hn
  have hmid := (hgeom (f a) haU.1.2.2 (n:ℕ) hng).1
    (sourcePeriodicMidpoint_mem_segment (by simp) (by norm_num) (f a) (n:ℕ))
  have hs : B.diracSum n a ≠ 0 := B.diracSum_ne_zero_of_free_circle a n (by
    simpa only [Int.cast_natCast] using hmid)
  exact (analyticAt_const.mul ((ha (n:ℕ) hna (f a) haU.1.2.1).comp (hf a haU.1.1))).div
    ((B.analytic_diracSum n a haU.1.1).pow 2) (pow_ne_zero 2 hs)

theorem exists_local_canonicalRatio_Miura_alternative (B : HillHminusMiuraGapBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧
      U ⊆ B.source ∩ hillHminusCanonicalRatioDomain ∧ ∀ a ∈ U, ∀ n : ℕ+, N ≤ (n:ℕ) →
        hillHminusCanonicalActionRatio n a = 1 ∨ hillHminusCanonicalActionRatio n a = B.normalizedRatio n a := by
  obtain ⟨N,V,hV,hqV,hVD,ha⟩ := B.exists_local_normalizedRatio_common_analytic q hq hr
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  refine ⟨N,ball q r,isOpen_ball,mem_ball_self hrpos,fun a ha => hVD (hball ha),?_⟩
  intro a haU n hn
  by_cases hz : ∀ b ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n b = 0
  · exact Or.inl (by rw [hillHminusCanonicalActionRatio,if_pos hz])
  · have hne : ∃ b ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n b ≠ 0 := by simpa using hz
    have hcanon : AnalyticOnNhd ℂ (hillHminusCanonicalActionRatio n) (ball q r) :=
      (analyticOnNhd_hillHminusCanonicalActionRatio n).mono (fun b hb => (hVD (hball hb)).2)
    have he := hcanon.eqOn_of_preconnected_of_eventuallyEq ((ha n hn).mono hball)
      (convex_ball q r).isPreconnected (mem_ball_self hrpos) (B.canonicalRatio_eq_local_germ n q hq hr hne)
    exact Or.inr (he haU)

end NLS.KdV.HillHminusMiuraGapBall
