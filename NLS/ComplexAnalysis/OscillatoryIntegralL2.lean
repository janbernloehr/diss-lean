import NLS.ComplexAnalysis.OscillatoryIntegralParts
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! # The square-integrable derivative estimate behind Lemma G.2

The interval may have any nonnegative length. The endpoint values are kept
explicit: identifying their bound with a particular interval Sobolev norm
is a separate trace estimate, not an implicit norm convention.
-/
noncomputable section
open Set MeasureTheory
namespace NLS.ComplexAnalysis

/-- Cauchy--Schwarz on an interval, including length zero and merely L2 data. -/
theorem integral_norm_le_sqrt_length_mul_L2 (f : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 t))) :
    (∫ s in 0..t, ‖f s‖) ≤ Real.sqrt t * Real.sqrt (∫ s in 0..t, ‖f s‖^2) := by
  let μ := volume.restrict (Ioc (0 : ℝ) t)
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := memLp_const 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun s => norm_nonneg (f s)))
    (Filter.Eventually.of_forall (fun _ : ℝ => (by norm_num : (0 : ℝ) ≤ 1)))
    (by simpa using hf.norm) (by simpa using h1)
  have hm : μ.real Set.univ = t := by simp [μ,Measure.real,ht]
  simpa [intervalIntegral.integral_of_le ht,Real.sqrt_eq_rpow,Real.rpow_two,
    ← Measure.real_def,hm,max_eq_left ht,mul_comm] using h

/-- Monotonicity of the actual derivative energy under interval restriction. -/
theorem sqrt_integral_norm_sq_le_unit (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (t : Icc (0 : ℝ) 1) :
    Real.sqrt (∫ s in 0..t.val, ‖f s‖^2) ≤ Real.sqrt (∫ s in (0 : ℝ)..1, ‖f s‖^2) := by
  have hi : IntervalIntegrable (fun s => ‖f s‖^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_two_iff_integrable_sq hf.norm.aestronglyMeasurable).mp hf.norm)
  exact Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval le_rfl t.property.1
    t.property.2 (Filter.Eventually.of_forall (fun s => sq_nonneg ‖f s‖)) hi)

/-- The literal two endpoint terms and the sqrt(time) derivative term.
No continuity of the derivative and no periodic endpoint condition is needed. -/
theorem norm_oscillatoryIntegral_weighted_le_L2 (c : ℂ) (hc : c ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioc 0 t))) :
    Real.exp (-(|c.re| * t))*‖oscillatoryIntegral c t f‖ ≤
      (‖f 0‖+‖f t‖+Real.sqrt t * Real.sqrt (∫ s in 0..t, ‖deriv f s‖^2))/(2*‖c‖) := by
  have hi : IntervalIntegrable (deriv f) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr (hd.integrable (by norm_num))
  exact (norm_oscillatoryIntegral_weighted_le c hc t ht f hf hi).trans
    (div_le_div_of_nonneg_right (add_le_add le_rfl
      (integral_norm_le_sqrt_length_mul_L2 (deriv f) t ht hd)) (by positivity))

/-- The printed numerical factor follows whenever H controls both traces
and the derivative L2 norm. The Sobolev norm comparison remains explicit. -/
theorem norm_oscillatoryIntegral_weighted_le_of_trace_L2_bound
    (c : ℂ) (hc : c ≠ 0) (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioc 0 t)))
    (H : ℝ) (h0 : ‖f 0‖ ≤ H) (htf : ‖f t‖ ≤ H)
    (hD : Real.sqrt (∫ s in 0..t, ‖deriv f s‖^2) ≤ H) :
    Real.exp (-(|c.re| * t))*‖oscillatoryIntegral c t f‖ ≤
      (2+Real.sqrt t)/(2*‖c‖)*H := by
  apply (norm_oscillatoryIntegral_weighted_le_L2 c hc t ht f hf hd).trans
  calc
    _ ≤ (H+H+Real.sqrt t*H)/(2*‖c‖) :=
      div_le_div_of_nonneg_right (add_le_add (add_le_add h0 htf)
        (mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg _))) (by positivity)
    _ = _ := by ring

end NLS.ComplexAnalysis
