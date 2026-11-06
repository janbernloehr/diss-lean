import NLS.ComplexAnalysis.ShiftedSquareRootBounds

/-! # Fixing a square-root sheet by its real part

An exact square identity and a strict real-part sign determine the root,
without a separate anchor or an unspecified sign choice.
-/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.ComplexAnalysis

theorem eq_principalSqrt_of_sq_of_re_pos (w v : ℂ) (hsq : w^2 = v) (hw : 0 < w.re) :
    w = Complex.sqrt v := by
  have he : w^2 = (Complex.sqrt v)^2 := hsq.trans (complex_sqrt_sq v).symm
  rcases eq_or_eq_neg_of_sq_eq_sq w (Complex.sqrt v) he with h | h
  · exact h
  · have hn := re_sqrt_nonneg v
    have hh := congrArg Complex.re h
    simp only [neg_re] at hh
    linarith

theorem eq_neg_principalSqrt_of_sq_of_re_neg (w v : ℂ) (hsq : w^2 = v) (hw : w.re < 0) :
    w = -Complex.sqrt v := by
  have he := eq_principalSqrt_of_sq_of_re_pos (-w) v (by simpa only [neg_sq] using hsq)
    (by simpa only [neg_re,neg_pos] using hw)
  exact neg_eq_iff_eq_neg.mp he

end NLS.ComplexAnalysis
