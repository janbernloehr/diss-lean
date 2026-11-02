import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic

/-! # Norm control from a hyperbolic cosine and an imaginary strip -/
noncomputable section
namespace NLS.ComplexAnalysis
open Complex

theorem norm_le_two_norm_cosh_add_abs_im (w : ℂ) :
    ‖w‖ ≤ 2*‖cosh w‖+1+|w.im| := by
  have hpos (z : ℂ) (hz : 0 ≤ z.re) : z.re ≤ 2*‖cosh z‖+1 := by
    have he : exp z = 2*cosh z-exp (-z) := by
      rw [cosh]
      ring
    have hb := norm_sub_le (2*cosh z) (exp (-z))
    rw [← he,norm_exp,norm_mul,norm_ofNat,norm_exp,neg_re] at hb
    have hm : Real.exp (-z.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith [Real.add_one_le_exp z.re]
  have hre : |w.re| ≤ 2*‖cosh w‖+1 := by
    by_cases hw : 0 ≤ w.re
    · rw [abs_of_nonneg hw]
      exact hpos w hw
    · rw [abs_of_neg (lt_of_not_ge hw)]
      simpa only [neg_re,cosh_neg] using hpos (-w) (by simp only [neg_re];linarith)
  exact (norm_le_abs_re_add_abs_im w).trans (by linarith)

end NLS.ComplexAnalysis
