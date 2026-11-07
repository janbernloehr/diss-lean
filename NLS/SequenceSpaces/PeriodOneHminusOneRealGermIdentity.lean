import NLS.SequenceSpaces.PeriodOneHminusOneRealForm

/-! An analytic identity on a connected native complex source domain
follows from agreement merely as a germ on its physical real form. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS

theorem analytic_eqOn_of_real_periodOneHminus_germ
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hconn : IsPreconnected U)
    (q : PeriodOneHminusOne) (hq : q ∈ U) (hr : IsRealPeriodOneHminusOne q)
    (f g : PeriodOneHminusOne → ℂ) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, f a.val = g a.val) : EqOn f g U := by
  obtain ⟨r,hrpos,hrealball⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.mp hU q hq
  let t : ℝ := min r R
  have ht : 0 < t := lt_min hrpos hR
  have hVU : ball q t ⊆ U := (ball_subset_ball (min_le_right r R)).trans hRU
  have hreal (a : PeriodOneHminusOne) (ha : a ∈ ball q t) (har : IsRealPeriodOneHminusOne a) : f a = g a := by
    apply hrealball (a := ⟨a,har⟩)
    change dist a q < r
    exact (mem_ball.mp ha).trans_le (min_le_left r R)
  have hlocalV : EqOn f g (ball q t) := analytic_eqOn_of_real_periodOneHminus _ isOpen_ball
    (convex_ball q t).isPreconnected ⟨q,mem_ball_self ht,hr⟩ f g (hf.mono hVU) (hg.mono hVU) hreal
  have hlocal : f =ᶠ[𝓝 q] g := by
    filter_upwards [ball_mem_nhds q ht] with a ha
    exact hlocalV ha
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn hq hlocal

end NLS
