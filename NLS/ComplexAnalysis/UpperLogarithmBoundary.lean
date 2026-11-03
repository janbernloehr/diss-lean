import NLS.ComplexAnalysis.UpperTracePrimitiveExtension
import NLS.ComplexAnalysis.NormalizedLogChart

/-! # Finite upper boundary limits of a continuous logarithm

A nonzero boundary limit of the exponential fixes one local logarithm
on a connected upper half-disc. The original logarithm therefore has
a finite limit, with its additive period retained.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_upper_logarithm_boundary_limit (F : ℂ → ℂ) (x : ℝ) (m : ℂ)
    (hm : m ≠ 0) (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hexp : Tendsto (fun z => exp (F z)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 m)) :
    ∃ A : ℂ, Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 A) ∧ exp A = m := by
  have hratio : Tendsto (fun z => exp (F z) / m)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa only [div_self hm] using hexp.div_const m
  have hnear : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ), exp (F z) / m ∈ slitPlane :=
    hratio.eventually (isOpen_slitPlane.mem_nhds (by simp : (1 : ℂ) ∈ slitPlane))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  let U := ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im}
  let a : ℂ := (x : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I
  have ha : a ∈ U := by
    constructor
    · rw [mem_ball, dist_eq_norm]
      simp only [a, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
      linarith
    · change 0 < a.im
      simpa only [a, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add] using half_pos hρ
  let C := F a - log (exp (F a) / m)
  let G : ℂ → ℂ := fun z => log (exp (F z) / m) + C
  have hG : ContinuousOn G U := by
    apply ContinuousOn.add_const
    exact ((hF.mono (fun _ hz => hz.2)).cexp.div_const m).clog (fun z hz => hball hz)
  have heq : EqOn F G U := by
    refine continuousLogarithms_eqOn F G U
      ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
      (hF.mono (fun _ hz => hz.2)) hG ?_ a ha ?_
    · intro z hz
      dsimp only [G, C]
      rw [exp_add, exp_sub, exp_log (div_ne_zero (exp_ne_zero _) hm),
        exp_log (div_ne_zero (exp_ne_zero _) hm)]
      field_simp
    · dsimp only [G, C]
      ring
  have hlim : Tendsto G (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 C) := by
    have hl := (continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp hratio
    simpa only [G, Function.comp_def, log_one, zero_add] using hl.add_const C
  have hactual : Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 C) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ : (x : ℂ) ∈ ball (x : ℂ) ρ))]
      with z hz hzB
    exact (heq ⟨hzB, hz⟩).symm
  let := real_upper_nhds_neBot x
  exact ⟨C, hactual, tendsto_nhds_unique (continuous_exp.continuousAt.tendsto.comp hactual) hexp⟩

/-- Full upper limits at every real point form a continuous real
boundary function, even when the original function is singular there. -/
theorem continuous_real_boundary_of_upper_limits (F : ℂ → ℂ) (B : ℝ → ℂ)
    (hB : ∀ x : ℝ, Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x))) :
    Continuous B := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hB x) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hyC : (y : ℂ) ∈ ball (x : ℂ) δ := by
    simpa only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      Real.dist_eq] using hy
  let := real_upper_nhds_neBot y
  have he : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (y : ℂ), dist (F z) (B x) ≤ ε / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hyC)] with z hz hzB
    exact (hb hz (mem_ball.mp hzB)).le
  have hle := le_of_tendsto ((hB y).dist (tendsto_const_nhds (x := B x))) he
  linarith

end NLS.ComplexAnalysis
