import NLS.FunctionalAnalysis.VariableGronwall

/-! # Integral Gronwall with a variable coefficient and constant forcing

This form is used to control differences of actual solutions in the L2
potential norm. The coupling stays inside the integral.
-/
noncomputable section
open Set MeasureTheory
namespace NLS.FunctionalAnalysis

theorem le_exp_integral_of_le_const_add_integral
    (f a : ℝ → ℝ) (hf : Continuous f) (ha : Continuous a) (T A : ℝ) (hA : 0 ≤ A)
    (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) (ha0 : ∀ t ∈ Icc 0 T, 0 ≤ a t)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ A+∫ s in (0:ℝ)..t, a s*f s) :
    ∀ t ∈ Icc 0 T, f t ≤ A*Real.exp (∫ s in (0:ℝ)..t, a s) := by
  let g (t : ℝ) := A+∫ s in (0:ℝ)..t, a s*f s
  have hd (t : ℝ) : HasDerivAt g (a t*f t) t :=
    (intervalIntegral.integral_hasDerivAt_right ((ha.mul hf).intervalIntegrable 0 t)
      (ha.mul hf).stronglyMeasurable.stronglyMeasurableAtFilter (ha.mul hf).continuousAt).const_add A
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have h := norm_le_exp_integral_of_norm_deriv_le (a := 0) (b := T)
    hg.continuousOn (fun t _ => (hd t).hasDerivWithinAt) ha (by
      intro t ht
      have ht' : t ∈ Icc 0 T := ⟨ht.1,ht.2.le⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (ha0 t ht') (hf0 t ht'))]
      exact mul_le_mul_of_nonneg_left ((hbound t ht').trans (le_abs_self (g t))) (ha0 t ht'))
  intro t ht
  have hb : ‖g t‖ ≤ A*Real.exp (∫ s in (0:ℝ)..t, a s) := by
    simpa only [g,intervalIntegral.integral_same,add_zero,Real.norm_eq_abs,abs_of_nonneg hA] using h t ht
  exact (hbound t ht).trans ((le_abs_self (g t)).trans hb)

end NLS.FunctionalAnalysis
