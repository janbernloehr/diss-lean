import NLS.KdV.HillHminusOneTraceChartSource
import NLS.KdV.HillHminusOneAllBoundaryLimits

/-! # Actual real boundary agreement of joint H^-1 trace charts

Upper and lower source agreement on a real-centered disc identifies the
whole actual boundary extension there, by its full upper limit. The two
connected half-discs keep both source sheets fixed for nearby real inputs.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminus_trace_chart_eq_realCut_on_ball
    (p : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne p)
    (x ρ : ℝ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (ball (x : ℂ) ρ))
    (hu : EqOn F (fun z => hillHminusContinuedPrimitive (z,p))
      (ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im}))
    (hl : EqOn F (fun z => hillHminusContinuedPrimitive (z,p))
      (ball (x : ℂ) ρ ∩ {z : ℂ | z.im < 0})) :
    EqOn F (hillHminusRealCutPrimitive p) (ball (x : ℂ) ρ) := by
  intro z hz
  by_cases hi : z.im = 0
  · have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have hy : (z.re : ℂ) ∈ ball (x : ℂ) ρ := by rw [← hzC]; exact hz
    have ht : Tendsto (fun w => hillHminusContinuedPrimitive (w,p))
        (𝓝[{w : ℂ | 0 < w.im}] (z.re : ℂ)) (𝓝 (F (z.re : ℂ))) := by
      apply ((hF _ hy).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds hy)] with w hw hwB
      exact hu ⟨hwB,hw⟩
    let := real_upper_nhds_neBot z.re
    have he := tendsto_nhds_unique ht (tendsto_hillHminusUpperBoundaryPrimitive_all p hr z.re)
    rw [hillHminusRealCutPrimitive,if_pos hi]
    simpa only [← hzC] using he
  · rw [hillHminusRealCutPrimitive,if_neg hi]
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · exact hl ⟨hz,hneg⟩
    · exact hu ⟨hz,hpos⟩

theorem exists_hillHminus_trace_chart_real_ball_agreement
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (Ω : Set ℂ) (V : Set PeriodOneHminusOne) (hΩ : IsOpen Ω) (hV : IsOpen V) (hq : q ∈ V)
    (F : ℂ × PeriodOneHminusOne → ℂ) (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V))
    (hbase : ∀ z ∈ Ω, F (z,q) = hillHminusRealCutPrimitive q z)
    (htrace : ∀ t ∈ Ω ×ˢ V, 2*cosh (F t) = hillHminusDiscriminant t.2 t.1 ∧ sinh (F t) ≠ 0)
    (x : ℝ) (hx : (x : ℂ) ∈ Ω) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (x : ℂ) ρ ⊆ Ω ∧
      ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ q ∈ W ∧ W ⊆ V ∧
        ∀ p ∈ W, IsRealPeriodOneHminusOne p →
          EqOn (fun z => F (z,p)) (hillHminusRealCutPrimitive p) (ball (x : ℂ) ρ) := by
  obtain ⟨ρ,hρ,hB⟩ := Metric.isOpen_iff.mp hΩ (x : ℂ) hx
  let U := ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im}
  let L := ball (x : ℂ) ρ ∩ {z : ℂ | z.im < 0}
  let a : ℂ := (x : ℂ) + ((ρ/2 : ℝ) : ℂ)*I
  let b : ℂ := (x : ℂ) - ((ρ/2 : ℝ) : ℂ)*I
  have haB : a ∈ ball (x : ℂ) ρ := by
    rw [mem_ball,dist_eq_norm]
    simp only [a,add_sub_cancel_left,norm_mul,norm_I,mul_one,norm_real,Real.norm_eq_abs,
      abs_of_pos (half_pos hρ)]
    linarith
  have hbB : b ∈ ball (x : ℂ) ρ := by
    rw [mem_ball,dist_eq_norm]
    have he : b - (x : ℂ) = -(((ρ/2 : ℝ) : ℂ)*I) := by dsimp only [b]; ring
    rw [he,norm_neg,norm_mul,norm_I,mul_one,norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hρ)]
    linarith
  have ha : a ∈ U := by
    refine ⟨haB,?_⟩
    change 0 < a.im
    simpa only [a,add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,zero_add,add_zero]
      using half_pos hρ
  have hb : b ∈ L := by
    refine ⟨hbB,?_⟩
    change b.im < 0
    simp only [b,sub_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero]
    linarith
  obtain ⟨Wu,hWu,hqu,hWuV,hu⟩ := exists_hillHminus_trace_chart_source_eqOn q hr Ω V hΩ hV hq F
    hF hbase htrace U ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
    (fun _ hz => hB hz.1) (fun _ hz => hz.2.ne') a ha
  obtain ⟨Wl,hWl,hql,hWlV,hl⟩ := exists_hillHminus_trace_chart_source_eqOn q hr Ω V hΩ hV hq F
    hF hbase htrace L ((convex_ball _ _).inter (convex_halfSpace_im_lt 0)).isPreconnected
    (fun _ hz => hB hz.1) (fun _ hz => hz.2.ne) b hb
  refine ⟨ρ,hρ,hB,Wu ∩ Wl,hWu.inter hWl,⟨hqu,hql⟩,fun p hp => hWuV hp.1,?_⟩
  intro p hp hpr
  apply hillHminus_trace_chart_eq_realCut_on_ball p hpr x ρ (fun z => F (z,p)) _
    (hu p hp.1 hpr) (hl p hp.2 hpr)
  intro z hz
  exact (hF (z,p) ⟨hB hz,hWuV hp.1⟩).comp (f := fun z : ℂ => (z,p))
    (analyticAt_id.prod analyticAt_const)

end NLS.KdV
