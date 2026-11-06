import NLS.KdV.HillHminusOneJointContourPrimitive
import NLS.ComplexAnalysis.ScalarCoordinateUniqueness

/-! # Source agreement of joint H^-1 trace charts on nonreal components

Local inverse uniqueness fixes the full source logarithm at a nonreal
anchor. Analytic identity propagates it across a connected energy chart
for every nearby real potential. No simple endpoint is required.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminus_trace_chart_source_germ
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (Ω : Set ℂ) (V : Set PeriodOneHminusOne) (hΩ : IsOpen Ω) (hV : IsOpen V) (hq : q ∈ V)
    (F : ℂ × PeriodOneHminusOne → ℂ) (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V))
    (hbase : ∀ z ∈ Ω, F (z,q) = hillHminusRealCutPrimitive q z)
    (htrace : ∀ t ∈ Ω ×ˢ V, 2*cosh (F t) = hillHminusDiscriminant t.2 t.1 ∧ sinh (F t) ≠ 0)
    (a : ℂ) (ha : a ∈ Ω) (hai : a.im ≠ 0) :
    F =ᶠ[𝓝 (a,q)] hillHminusContinuedPrimitive := by
  have hs := mem_hillHminusContinuationDomain_of_im_ne_zero q hr a hai
  have hb : F (a,q) = hillHminusContinuedPrimitive (a,q) := by
    rw [hbase a ha,hillHminusRealCutPrimitive,if_neg hai]
  apply eventuallyEq_of_regular_scalar_coordinate cosh F hillHminusContinuedPrimitive (a,q)
    Complex.analyticAt_cosh
  · rw [(Complex.hasDerivAt_cosh _).deriv,← hb]
    exact (htrace (a,q) ⟨ha,hq⟩).2
  · exact (hF (a,q) ⟨ha,hq⟩).continuousAt
  · exact (analyticOnNhd_hillHminusContinuedPrimitive _ hs).continuousAt
  · exact hb
  · filter_upwards [(hΩ.prod hV).mem_nhds ⟨ha,hq⟩,
      isOpen_hillHminusContinuationDomain.mem_nhds hs] with t ht hts
    have hG := (htrace t ht).1
    have hS := (hillHminusContinuedPrimitive_trace t hts).1
    linear_combination (hG-hS)/2

theorem exists_hillHminus_trace_chart_source_eqOn
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (Ω : Set ℂ) (V : Set PeriodOneHminusOne) (hΩ : IsOpen Ω) (hV : IsOpen V) (hq : q ∈ V)
    (F : ℂ × PeriodOneHminusOne → ℂ) (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V))
    (hbase : ∀ z ∈ Ω, F (z,q) = hillHminusRealCutPrimitive q z)
    (htrace : ∀ t ∈ Ω ×ˢ V, 2*cosh (F t) = hillHminusDiscriminant t.2 t.1 ∧ sinh (F t) ≠ 0)
    (U : Set ℂ) (hconn : IsPreconnected U) (hUΩ : U ⊆ Ω)
    (hUi : ∀ z ∈ U, z.im ≠ 0) (a : ℂ) (ha : a ∈ U) :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ q ∈ W ∧ W ⊆ V ∧
      ∀ p ∈ W, IsRealPeriodOneHminusOne p →
        EqOn (fun z => F (z,p)) (fun z => hillHminusContinuedPrimitive (z,p)) U := by
  have he := hillHminus_trace_chart_source_germ q hr Ω V hΩ hV hq F hF hbase htrace
    a (hUΩ ha) (hUi a ha)
  rw [nhds_prod_eq] at he
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_prod_iff.mp he
  have hnearV : ∀ᶠ p in 𝓝 q, p ∈ B ∩ V := inter_mem hB (hV.mem_nhds hq)
  obtain ⟨W,hW,hWo,hqW⟩ := _root_.eventually_nhds_iff.mp hnearV
  refine ⟨W,hWo,hqW,fun p hp => (hW p hp).2,?_⟩
  intro p hp hpr
  have hGp : AnalyticOnNhd ℂ (fun z => F (z,p)) U := by
    intro z hz
    exact (hF (z,p) ⟨hUΩ hz,(hW p hp).2⟩).comp (f := fun z : ℂ => (z,p))
      (analyticAt_id.prod analyticAt_const)
  have hSp := (analyticOnNhd_hillHminusContinuedPrimitive_off_real p hpr).mono hUi
  have hnear : (fun z => F (z,p)) =ᶠ[𝓝 a] (fun z => hillHminusContinuedPrimitive (z,p)) := by
    filter_upwards [hA] with z hz
    exact hAB ⟨hz,(hW p hp).1⟩
  exact hGp.eqOn_of_preconnected_of_eventuallyEq hSp hconn ha hnear

end NLS.KdV
