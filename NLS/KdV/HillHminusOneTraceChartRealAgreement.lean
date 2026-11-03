import NLS.KdV.HillHminusOneTraceChartBoundary

/-! # Uniform actual real-potential agreement on compact H^-1 trace collars

Local source matching and full real boundary limits give agreement in a
product neighborhood of each reference energy. Compactness chooses one
potential neighborhood before all points of the integration circle.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_trace_chart_local_real_agreement
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (Ω : Set ℂ) (V : Set PeriodOneHminusOne) (hΩ : IsOpen Ω) (hV : IsOpen V) (hq : q ∈ V)
    (F : ℂ × PeriodOneHminusOne → ℂ) (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V))
    (hbase : ∀ z ∈ Ω, F (z,q) = hillHminusRealCutPrimitive q z)
    (htrace : ∀ t ∈ Ω ×ˢ V, 2*cosh (F t) = hillHminusDiscriminant t.2 t.1 ∧ sinh (F t) ≠ 0)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Ω) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ q ∈ W ∧ W ⊆ V ∧
      ∀ p ∈ W, IsRealPeriodOneHminusOne p →
        EqOn (fun z => F (z,p)) (hillHminusRealCutPrimitive p) (ball z₀ ρ) := by
  by_cases hi : z₀.im = 0
  · have hzC : z₀ = (z₀.re : ℂ) := by apply Complex.ext <;> simp [hi]
    obtain ⟨ρ,hρ,_,W,hW,hqW,hWV,heq⟩ := exists_hillHminus_trace_chart_real_ball_agreement
      q hr Ω V hΩ hV hq F hF hbase htrace z₀.re (by rwa [← hzC])
    refine ⟨ρ,hρ,W,hW,hqW,hWV,?_⟩
    intro p hp hpr z hz
    exact heq p hp hpr (by simpa only [← hzC] using hz)
  · have ho : IsOpen (Ω ∩ {z : ℂ | z.im ≠ 0}) :=
      hΩ.inter (isOpen_ne_fun continuous_im continuous_const)
    obtain ⟨ρ,hρ,hB⟩ := Metric.isOpen_iff.mp ho z₀ ⟨hz₀,hi⟩
    obtain ⟨W,hW,hqW,hWV,heq⟩ := exists_hillHminus_trace_chart_source_eqOn q hr Ω V hΩ hV hq F
      hF hbase htrace (ball z₀ ρ) (convex_ball _ _).isPreconnected
      (fun _ hz => (hB hz).1) (fun _ hz => (hB hz).2) z₀ (mem_ball_self hρ)
    refine ⟨ρ,hρ,W,hW,hqW,hWV,?_⟩
    intro p hp hpr z hz
    rw [hillHminusRealCutPrimitive,if_neg (hB hz).2]
    exact heq p hp hpr hz

theorem exists_hillHminus_trace_chart_compact_real_agreement
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (Ω : Set ℂ) (V : Set PeriodOneHminusOne) (hΩ : IsOpen Ω) (hV : IsOpen V) (hq : q ∈ V)
    (F : ℂ × PeriodOneHminusOne → ℂ) (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V))
    (hbase : ∀ z ∈ Ω, F (z,q) = hillHminusRealCutPrimitive q z)
    (htrace : ∀ t ∈ Ω ×ˢ V, 2*cosh (F t) = hillHminusDiscriminant t.2 t.1 ∧ sinh (F t) ≠ 0)
    (S : Set ℂ) (hS : IsCompact S) (hSΩ : S ⊆ Ω) :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ q ∈ W ∧ W ⊆ V ∧
      ∀ p ∈ W, IsRealPeriodOneHminusOne p →
        EqOn (fun z => F (z,p)) (hillHminusRealCutPrimitive p) S := by
  have hlocal (z : ℂ) (hz : z ∈ S) :
      ∀ᶠ t : PeriodOneHminusOne × ℂ in 𝓝 (q,z),
        IsRealPeriodOneHminusOne t.1 → F (t.2,t.1) = hillHminusRealCutPrimitive t.1 t.2 := by
    obtain ⟨ρ,hρ,W,hW,hqW,_,heq⟩ := exists_hillHminus_trace_chart_local_real_agreement
      q hr Ω V hΩ hV hq F hF hbase htrace z (hSΩ hz)
    filter_upwards [(hW.prod isOpen_ball).mem_nhds ⟨hqW,mem_ball_self hρ⟩] with t ht
    exact fun hpr => heq t.1 ht.1 hpr ht.2
  have hall := hS.eventually_forall_of_forall_eventually (x₀ := q)
    (P := fun p z => IsRealPeriodOneHminusOne p → F (z,p) = hillHminusRealCutPrimitive p z) hlocal
  have hboth : ∀ᶠ p in 𝓝 q, p ∈ V ∧
      ∀ z ∈ S, IsRealPeriodOneHminusOne p → F (z,p) = hillHminusRealCutPrimitive p z := by
    filter_upwards [hall,hV.mem_nhds hq] with p hp hpV
    exact ⟨hpV,hp⟩
  obtain ⟨W,hW,hWo,hqW⟩ := _root_.eventually_nhds_iff.mp hboth
  refine ⟨W,hWo,hqW,fun p hp => (hW p hp).1,?_⟩
  intro p hp hpr z hz
  exact (hW p hp).2 z hz hpr

end NLS.KdV
