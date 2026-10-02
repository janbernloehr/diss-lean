import NLS.ComplexAnalysis.ScalarDuhamel
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Positivity

/-! # Exponentially normalized Duhamel integral bounds

A common real growth bound on the free exponent transfers through
integration exactly, leaving the same weight on the forcing at its
own time. Both spectral half-planes share this estimate.
-/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- Normalize a free propagator by any upper bound on its real
exponent. The forcing majorant need only be continuous. -/
theorem norm_exp_integral_weighted_le
    (c : ℂ) (a t : ℝ) (hc : c.re ≤ a) (ht : 0 ≤ t)
    (f : ℝ → ℂ) (g : ℝ → ℝ) (hg : Continuous g)
    (hfg : ∀ s ∈ Icc 0 t, ‖f s‖ ≤ g s) :
    Real.exp (-a*t)*‖∫ s in (0 : ℝ)..t, exp (c*((t-s : ℝ) : ℂ))*f s‖ ≤
      ∫ s in (0 : ℝ)..t, Real.exp (-a*s)*g s := by
  have hkernel (s : ℝ) (hs : s ∈ Icc 0 t) :
      ‖exp (c*((t-s : ℝ) : ℂ))‖ ≤ Real.exp (a*(t-s)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using
      mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hs.2)
  have hmajor : ‖∫ s in (0 : ℝ)..t, exp (c*((t-s : ℝ) : ℂ))*f s‖ ≤
      ∫ s in (0 : ℝ)..t, Real.exp (a*(t-s))*g s := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht
    · filter_upwards [] with s hs
      rw [norm_mul]
      exact mul_le_mul (hkernel s ⟨hs.1.le,hs.2⟩) (hfg s ⟨hs.1.le,hs.2⟩)
        (norm_nonneg _) (Real.exp_nonneg _)
    · exact (show Continuous (fun s : ℝ => Real.exp (a*(t-s))*g s) by fun_prop).intervalIntegrable _ _
  have h := mul_le_mul_of_nonneg_left hmajor (Real.exp_nonneg (-a*t))
  refine h.trans_eq ?_
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← mul_assoc,← Real.exp_add]
  congr 2
  ring

end NLS.ComplexAnalysis
