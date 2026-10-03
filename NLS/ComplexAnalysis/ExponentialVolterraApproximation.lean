import NLS.ComplexAnalysis.ExponentialVolterra
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # The exponential Volterra kernel as an approximate identity

At a positive time, multiplying the causal convolution by its decay rate
recovers the continuous forcing. The endpoint zero is deliberately excluded.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral Filter Topology Metric
namespace NLS.ComplexAnalysis

private theorem tendsto_rate_mul_exp_neg (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun a : ℝ => a * Real.exp (-a*δ)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.atTop_mul_const hδ)).div_const δ
  convert h using 1
  · ext a
    simp only [pow_one, Function.comp_apply, id_eq, neg_mul]
    field_simp
  · simp

/-- A normalized causal exponential convolution recovers a continuous
forcing at every strictly positive time. -/
theorem tendsto_scaled_exponentialVolterra {f : ℝ → ℂ} (hf : Continuous f)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun a : ℝ => (a : ℂ) * exponentialVolterra (-a) f t) atTop (𝓝 (f t)) := by
  let k := fun a s : ℝ => a * Real.exp (-a * (t-s))
  have hk (a : ℝ) : Continuous (k a) := by dsimp [k]; fun_prop
  have hi : Tendsto (fun a : ℝ => ∫ s in Icc 0 t, k a s) atTop (𝓝 1) := by
    have he : Tendsto (fun a : ℝ => Real.exp (-a*t)) atTop (𝓝 0) :=
      by simpa only [Function.comp_def, id_eq, neg_mul] using
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const ht))
    have hh : Tendsto (fun a : ℝ => 1 - Real.exp (-a*t)) atTop (𝓝 1) := by
      simpa only [sub_zero] using he.const_sub 1
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.le]
    dsimp [k]
    rw [intervalIntegral.integral_const_mul, integral_decaying_kernel a t ha ht.le]
    field_simp
  have hl : ∀ u : Set ℝ, IsOpen u → t ∈ u → TendstoUniformlyOn k 0 atTop (Icc 0 t \ u) := by
    intro u hu htu
    obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hu t htu
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (tendsto_rate_mul_exp_neg δ hδ).eventually (gt_mem_nhds hε)] with a ha hea
    intro s hs
    have hdist : δ ≤ dist s t := le_of_not_gt (fun h => hs.2 (hball h))
    have hst : δ ≤ t-s := by
      simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.1.2), neg_sub] using hdist
    have hnonneg : 0 ≤ k a s := by dsimp [k]; positivity
    simp only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    apply lt_of_le_of_lt _ hea
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) ha.le
  have hp := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    (μ := volume) (s := Icc 0 t) (t := Icc 0 t) (x₀ := t) (φ := k)
    measurableSet_Icc measurableSet_Icc (Subset.rfl) self_mem_nhdsWithin
    (measure_Icc_lt_top.ne)
    (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha s _; dsimp [k]; positivity)
    hl hi (Eventually.of_forall (fun a => (hk a).aestronglyMeasurable))
    (hf.integrableOn_Icc) hf.continuousAt.continuousWithinAt
  convert hp using 1
  ext a
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.le,
    exponentialVolterra, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp [k]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_sub, mul_assoc]

/-- Integration against another continuous factor preserves the approximate
identity limit. The fixed bound on the forcing supplies domination even near zero. -/
theorem tendsto_integral_mul_scaled_exponentialVolterra {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ s ∈ Icc (0 : ℝ) 1, ‖g s‖ ≤ M) :
    Tendsto (fun a : ℝ => ∫ s in (0 : ℝ)..1,
      f s * ((a : ℂ) * exponentialVolterra (-a) g s)) atTop
      (𝓝 (∫ s in (0 : ℝ)..1, f s * g s)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun s => ‖f s‖ * M)
  · exact Eventually.of_forall (fun a =>
      (hf.mul (continuous_const.mul (continuous_exponentialVolterra _ hg))).aestronglyMeasurable)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    apply Eventually.of_forall
    intro s hs
    have hs' : s ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
    have hb := norm_exponentialVolterra_le (-a) a s M ha hs'.1.le hM (by simp) g
      (fun r hr => hgb r ⟨hr.1, hr.2.trans hs'.2⟩)
    have hscale : ‖(a : ℂ) * exponentialVolterra (-a) g s‖ ≤ M := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
      calc
        _ ≤ a * (M/a) := mul_le_mul_of_nonneg_left hb ha.le
        _ = M := by field_simp
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hscale (norm_nonneg _)
  · exact (hf.norm.mul continuous_const).intervalIntegrable 0 1
  · apply Eventually.of_forall
    intro s hs
    have hs' : s ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
    exact (tendsto_scaled_exponentialVolterra hg s hs'.1).const_mul (f s)

end NLS.ComplexAnalysis
