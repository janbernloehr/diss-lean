import NLS.FunctionalAnalysis.VariableGronwall

/-! # Integral Gronwall for a nonnegative error

A continuous error bounded by a constant forcing plus the integral
of itself is dominated by the corresponding exponential. No bound
on the unknown error is supplied as a premise.
-/

noncomputable section
open Set MeasureTheory
namespace NLS.FunctionalAnalysis

/-- Close a Volterra norm estimate on a finite interval, including
zero forcing and zero coupling. -/
theorem le_exp_of_le_const_add_integral
    (f : ℝ → ℝ) (hf : Continuous f) (T A M : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ A+M*(∫ s in (0 : ℝ)..t, f s)) :
    ∀ t ∈ Icc 0 T, f t ≤ A*Real.exp (M*t) := by
  let g (t : ℝ) := A+M*(∫ s in (0 : ℝ)..t, f s)
  have hd (t : ℝ) : HasDerivAt g (M*f t) t := by
    exact ((intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_mul M).const_add A
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have h := norm_le_exp_integral_of_norm_deriv_le (a := 0) (b := T)
    hg.continuousOn (fun t _ => (hd t).hasDerivWithinAt)
    (α := fun _ => M) continuous_const (by
      intro t ht
      have ht' : t ∈ Icc 0 T := ⟨ht.1,ht.2.le⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hM (hpos t ht'))]
      exact mul_le_mul_of_nonneg_left ((hbound t ht').trans (le_abs_self (g t))) hM)
  intro t ht
  have hb : ‖g t‖ ≤ A*Real.exp (M*t) := by
    simpa only [g,intervalIntegral.integral_same,mul_zero,add_zero,Real.norm_eq_abs,
      abs_of_nonneg hA,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm t M] using h t ht
  exact (hbound t ht).trans ((le_abs_self (g t)).trans hb)

end NLS.FunctionalAnalysis
