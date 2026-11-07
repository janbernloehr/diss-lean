import NLS.KdV.HminusOneCanonicalHillPsiZeros

/-! Distinct original retained labels of the SAME intrinsic numerator
remain distinct on their ENTIRE common complex domains. A collision of
simple analytic roots would force equality on a connected chart overlap,
which contains a real source with disjoint original indexed gaps. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusCanonicalPsiRealZero_injective (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : Function.Injective (fun m : ℕ+ => hillHminusCanonicalPsiRealZero n m q hr) := by
  intro i j he
  by_contra hne
  have hi := hillHminusCanonicalPsiRealZero_mem_gap n i q hr
  have hj := hillHminusCanonicalPsiRealZero_mem_gap n j q hr
  change hillHminusCanonicalPsiRealZero n i q hr = hillHminusCanonicalPsiRealZero n j q hr at he
  rw [← he] at hj
  exact Set.disjoint_left.mp (hillHminusOriginal_positive_gaps_disjoint q hr i j hne) hi hj

theorem HillHminusPsiZeroBall.values_ne_on_overlap {n m k : ℕ+}
    (B : HillHminusPsiZeroBall n m) (C : HillHminusPsiZeroBall n k) (hmk : m ≠ k)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source ∩ C.source) : B.value q ≠ C.value q := by
  intro heq
  have hF := analyticOnNhd_hillHminusCanonicalPsi n (B.value q,q) ⟨mem_univ _,B.subset hq.1⟩
  have hd : (fderiv ℂ (hillHminusCanonicalPsi n) (B.value q,q)) (1,0) ≠ 0 := by
    rw [← deriv_spectral_section_eq_fderiv (hillHminusCanonicalPsi n) (B.value q) q hF.differentiableAt]
    exact B.simple q hq.1
  have hnear : ∀ᶠ a in 𝓝 q, a ∈ B.source ∩ C.source :=
    (B.source_open.inter C.source_open).mem_nhds hq
  have hlocal : B.value =ᶠ[𝓝 q] C.value := by
    apply eventually_eq_of_continuous_simple_root_selections (hillHminusCanonicalPsi n)
      id B.value C.value q hF continuousAt_id (B.analytic_value q hq.1).continuousAt
      (C.analytic_value q hq.2).continuousAt heq _ _ hd
    · filter_upwards [hnear] with a ha
      exact B.root a ha.1
    · filter_upwards [hnear] with a ha
      exact C.root a ha.2
  have hwhole : EqOn B.value C.value (B.source ∩ C.source) :=
    (B.analytic_value.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      (C.analytic_value.mono inter_subset_right)
      ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hq hlocal
  obtain ⟨a,ha,har⟩ := exists_real_mem_periodOneHminus_ball_inter B.center C.center
    B.center_real C.center_real B.radius C.radius ⟨q,hq⟩
  have he : (hillHminusCanonicalPsiRealZero n m a har:ℂ) = (hillHminusCanonicalPsiRealZero n k a har:ℂ) := by
    rw [← B.real_eq a ha.1 har,← C.real_eq a ha.2 har]
    exact hwhole ha
  exact hmk (hillHminusCanonicalPsiRealZero_injective n a har (Complex.ofReal_inj.mp he))

theorem hillHminusCanonicalRetainedPsiZero_ne (n m k : ℕ+) (hmk : m ≠ k)
    (q : PeriodOneHminusOne) (hm : q ∈ hillHminusPsiZeroDomain n m) (hk : q ∈ hillHminusPsiZeroDomain n k) :
    hillHminusCanonicalRetainedPsiZero n m q ≠ hillHminusCanonicalRetainedPsiZero n k q := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hm
  obtain ⟨C,hC⟩ := mem_iUnion.mp hk
  rw [B.canonical_zero_eq q hB,C.canonical_zero_eq q hC]
  exact B.values_ne_on_overlap C hmk q ⟨hB,hC⟩

end NLS.KdV
