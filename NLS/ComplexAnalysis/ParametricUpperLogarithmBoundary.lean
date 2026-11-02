import NLS.ComplexAnalysis.UpperLogarithmBoundary

/-! # Continuity of the boundary period in a logarithm family

When the exponential tends jointly to the same nonzero value, the
boundary logarithm cannot change its integer period as a parameter
varies. A fixed positive-height anchor gives a local continuous formula.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem continuous_boundary_logarithm_of_constant_exponential
    {T : Type*} [TopologicalSpace T] (F : T → ℝ → ℂ) (B : T → ℂ) (m : ℂ) (hm : m ≠ 0)
    (hpar : ∀ ε : ℝ, 0 < ε → Continuous (fun t => F t ε))
    (hvert : ∀ t, ContinuousOn (F t) (Ioi 0))
    (hlim : ∀ t, Tendsto (F t) (𝓝[>] 0) (𝓝 (B t)))
    (hbase : ∀ t, exp (B t) = m)
    (hjoint : ∀ t, Tendsto (fun p : T × ℝ => exp (F p.1 p.2))
      (𝓝 t ×ˢ 𝓝[>] 0) (𝓝 m)) : Continuous B := by
  apply continuous_iff_continuousAt.mpr
  intro t0
  have hr : Tendsto (fun p : T × ℝ => exp (F p.1 p.2) / m)
      (𝓝 t0 ×ˢ 𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    simpa only [div_self hm] using (hjoint t0).div_const m
  obtain ⟨s, hs, v, hv, hsv⟩ := mem_prod_iff.mp
    (hr.eventually (isOpen_slitPlane.mem_nhds (by simp : (1 : ℂ) ∈ slitPlane)))
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hv
  have hslit (t : T) (ht : t ∈ s) (ε : ℝ) (hε : ε ∈ Ioo 0 δ) :
      exp (F t ε) / m ∈ slitPlane := by
    have hvε : ε ∈ v := by
      apply hd
      refine ⟨?_, hε.1⟩
      simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε.1] using hε.2
    exact hsv (a := (t, ε)) ⟨ht, hvε⟩
  let a := δ / 2
  have ha : a ∈ Ioo 0 δ := ⟨half_pos hδ, by dsimp [a]; linarith⟩
  let C : T → ℂ := fun t => F t a - log (exp (F t a) / m)
  have hformula (t : T) (ht : t ∈ s) : B t = C t := by
    let G : ℝ → ℂ := fun ε => log (exp (F t ε) / m) + C t
    have hG : ContinuousOn G (Ioo 0 δ) :=
      (((hvert t).mono (fun _ hz => hz.1)).cexp.div_const m).clog
        (fun ε hε => hslit t ht ε hε) |>.add_const _
    have heq : EqOn (F t) G (Ioo 0 δ) := by
      refine continuousLogarithms_eqOn (F t) G (Ioo 0 δ) isPreconnected_Ioo
        ((hvert t).mono (fun _ hz => hz.1)) hG ?_ a ha ?_
      · intro ε hε
        dsimp only [G, C]
        rw [exp_add, exp_sub, exp_log (div_ne_zero (exp_ne_zero _) hm),
          exp_log (div_ne_zero (exp_ne_zero _) hm)]
        field_simp
      · dsimp only [G, C]
        ring
    have hratio : Tendsto (fun ε => exp (F t ε) / m) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
      simpa only [Function.comp_def, hbase t, div_self hm] using
        (continuous_exp.continuousAt.tendsto.comp (hlim t)).div_const m
    have hGlim : Tendsto G (𝓝[>] 0) (𝓝 (C t)) := by
      have hl := (continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp hratio
      simpa only [G, Function.comp_def, log_one, zero_add] using hl.add_const (C t)
    have hFactual : Tendsto (F t) (𝓝[>] 0) (𝓝 (C t)) := by
      apply hGlim.congr'
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
      exact (heq ⟨hε, hεδ⟩).symm
    exact tendsto_nhds_unique (hlim t) hFactual
  have hC : ContinuousAt C t0 := by
    have hFa : ContinuousAt (fun t => F t a) t0 := (hpar a ha.1).continuousAt
    exact hFa.sub ((hFa.cexp.div_const m).clog (hslit t0 (mem_of_mem_nhds hs) a ha))
  exact hC.congr_of_eventuallyEq (Filter.eventually_of_mem hs (fun t ht => hformula t ht))

end NLS.ComplexAnalysis
