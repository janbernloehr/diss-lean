import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Integral majorants on initial segments of the unit interval

A continuous integral majorant over the full period controls every initial segment for a Banach-valued integrand.
-/

noncomputable section
open Set MeasureTheory
namespace NLS.ComplexAnalysis

/-- An integrable majorant on the full period controls every initial segment. -/
theorem norm_integral_unit_le_mul_integral_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) (hg : Continuous g) (f : ℝ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x ∈ Icc (0:ℝ) 1, ‖g x‖ ≤ C*‖f x‖)
    (t : Icc (0:ℝ) 1) :
    ‖∫ x in (0:ℝ)..t.val, g x‖ ≤ C*(∫ x in (0:ℝ)..1, ‖f x‖) := by
  apply (intervalIntegral.norm_integral_le_integral_norm t.property.1).trans
  calc
    _ ≤ ∫ x in (0:ℝ)..t.val, C*‖f x‖ := by
      apply intervalIntegral.integral_mono_on t.property.1 (hg.norm.intervalIntegrable _ _)
        ((continuous_const.mul hf.norm).intervalIntegrable _ _)
      intro x hx
      exact hb x ⟨hx.1,hx.2.trans t.property.2⟩
    _ = C*(∫ x in (0:ℝ)..t.val, ‖f x‖) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
        (Filter.Eventually.of_forall (fun x => norm_nonneg _)) (hf.norm.intervalIntegrable 0 1)) hC

end NLS.ComplexAnalysis
