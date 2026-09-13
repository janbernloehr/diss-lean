import NLS.ComplexAnalysis.ScalarDuhamel
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Integral bounds for a decaying free kernel

The bounds depend only on the real part of the exponential coefficient.
They are therefore uniform in its oscillatory part.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
namespace NLS.ComplexAnalysis

theorem integral_decaying_kernel (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    (∫ s in 0..t, Real.exp (-a * (t - s))) = (1 - Real.exp (-a * t)) / a := by
  have hd (s : ℝ) : HasDerivAt (fun s => Real.exp (-a * (t - s)) / a)
      (Real.exp (-a * (t - s))) s := by
    convert! ((((hasDerivAt_id s).const_sub t).const_mul (-a)).exp.div_const a) using 1
    dsimp
    field_simp
  have hi := integral_eq_sub_of_hasDerivAt_of_le ht
    (show Continuous (fun s => Real.exp (-a * (t - s)) / a) by fun_prop).continuousOn
    (fun s _ => hd s)
    ((show Continuous (fun s => Real.exp (-a * (t - s))) by fun_prop).intervalIntegrable 0 t)
  simpa only [sub_self, mul_zero, Real.exp_zero, sub_zero, sub_div] using hi

theorem integral_decaying_kernel_le (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    (∫ s in 0..t, Real.exp (-a * (t - s))) ≤ 1 / a := by
  rw [integral_decaying_kernel a t ha ht]
  exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_nonneg _)) ha.le

/-- Exact norm of the propagator with a prescribed decay rate. -/
theorem norm_exp_propagator (c : ℂ) (a t s : ℝ) (hc : c.re = -a) :
    ‖exp (c * (t - s))‖ = Real.exp (-a * (t - s)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, hc]

/-- A bounded forcing gains an inverse decay rate under the Volterra kernel. -/
theorem norm_integral_exp_propagator_mul_le (c : ℂ) (a t M : ℝ)
    (ha : 0 < a) (ht : 0 ≤ t) (hM : 0 ≤ M) (hc : c.re = -a)
    (f : ℝ → ℂ) (hf : ∀ s ∈ Icc 0 t, ‖f s‖ ≤ M) :
    ‖∫ s in 0..t, exp (c * (t - s)) * f s‖ ≤ M / a := by
  have hi : ‖∫ s in 0..t, exp (c * (t - s)) * f s‖ ≤
      ∫ s in 0..t, Real.exp (-a * (t - s)) * M := by
    apply norm_integral_le_of_norm_le ht
    · apply Filter.Eventually.of_forall
      intro s hs
      rw [norm_mul, norm_exp_propagator c a t s hc]
      exact mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩) (Real.exp_nonneg _)
    · exact (show Continuous (fun s => Real.exp (-a * (t - s)) * M) by
        fun_prop).intervalIntegrable 0 t
  rw [intervalIntegral.integral_mul_const] at hi
  calc
    _ ≤ (∫ s in 0..t, Real.exp (-a * (t - s))) * M := hi
    _ ≤ (1 / a) * M := mul_le_mul_of_nonneg_right (integral_decaying_kernel_le a t ha ht) hM
    _ = M / a := by ring

/-- Quantitative Duhamel error for a stable scalar differential equation. -/
theorem norm_scalar_duhamel_sub_free_le (c : ℂ) (a t M : ℝ)
    (ha : 0 < a) (ht : 0 ≤ t) (hM : 0 ≤ M) (hc : c.re = -a)
    (u f : ℝ → ℂ) (hu : Continuous u) (hf : Continuous f)
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt u (c * u s + f s) s)
    (hb : ∀ s ∈ Icc 0 t, ‖f s‖ ≤ M) :
    ‖u t - exp (c * t) * u 0‖ ≤ M / a := by
  rw [scalar_duhamel c u f t ht hu hf hd, add_sub_cancel_left]
  exact norm_integral_exp_propagator_mul_le c a t M ha ht hM hc f hb

end NLS.ComplexAnalysis
