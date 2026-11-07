import NLS.KdV.HillDirichletSheetNontrivial

/-! The actual physical sheet is nontrivial in every nonempty open
subset of the common connected Dirichlet domain. Analytic identities
can therefore cancel it locally without division at its zero points. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminusDirichletSheet_ne_zero_in_open (m : ℕ+)
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hne : U.Nonempty)
    (hsub : U ⊆ hillHminusCanonicalDirichletDomain) :
    ∃ q ∈ U, hillHminusDirichletSheet m q ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨q,hq⟩ := hne
  have he : hillHminusDirichletSheet m =ᶠ[𝓝 q] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    exact hn p hp
  have heq := (analyticOnNhd_hillHminusDirichletSheet m).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : PeriodOneHminusOne => (0:ℂ)) hillHminusCanonicalDirichletDomain)
    isConnected_hillHminusCanonicalDirichletDomain.isPreconnected (hsub hq) he
  obtain ⟨a,ha,hna⟩ := exists_hillHminusDirichletSheet_ne_zero m
  exact hna (heq ha)

theorem hillHminusDirichletSheet_cancel_analytic (m : ℕ+)
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : U.Nonempty) (hsub : U ⊆ hillHminusCanonicalDirichletDomain)
    (F G : PeriodOneHminusOne → ℂ) (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (he : ∀ q ∈ U, hillHminusDirichletSheet m q*(F q-G q)=0) : EqOn F G U := by
  obtain ⟨a,ha,hna⟩ := exists_hillHminusDirichletSheet_ne_zero_in_open m U hU hne hsub
  exact analytic_eqOn_of_mul_sub_eq_zero U hU hconn F G (hillHminusDirichletSheet m)
    hF hG ((analyticOnNhd_hillHminusDirichletSheet m).mono hsub) a ha hna he

end NLS.KdV
