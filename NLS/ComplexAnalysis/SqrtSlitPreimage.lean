import Mathlib.Analysis.Complex.Basic

/-!
# The inverse image of the principal square-root cut under `1-z²`

If `1-z²` lies on the nonpositive real axis, then `z` is real and its
absolute value is at least one. This elementary geometry is the branch
cut calculation needed for standard periodic roots.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- The normalized quadratic radicand reaches the principal square-root
cut only for real arguments outside `(-1,1)`. -/
theorem real_abs_ge_one_of_one_sub_sq_not_mem_slitPlane (w : ℂ)
    (h : 1-w^2 ∉ Complex.slitPlane) :
    w.im = 0 ∧ 1 ≤ |w.re| := by
  have hnot := (not_or.mp ((Complex.mem_slitPlane_iff).not.mp h))
  have hre : (1-w^2).re ≤ 0 := le_of_not_gt hnot.1
  have him : (1-w^2).im = 0 := not_not.mp hnot.2
  have hre' : 1 - (w.re^2-w.im^2) ≤ 0 := by
    simpa only [Complex.sub_re, Complex.one_re, pow_two,
      Complex.mul_re] using hre
  have hprod : w.re*w.im = 0 := by
    simp only [Complex.sub_im, Complex.one_im, pow_two,
      Complex.mul_im] at him
    nlinarith
  have hy : w.im = 0 := by
    by_contra hne
    have hx : w.re = 0 := (mul_eq_zero.mp hprod).resolve_right hne
    nlinarith [sq_nonneg w.im]
  refine ⟨hy, ?_⟩
  by_cases hx : 0 ≤ w.re
  · rw [abs_of_nonneg hx]
    nlinarith [hre']
  · rw [abs_of_neg (lt_of_not_ge hx)]
    nlinarith [hre']

/-- A point off the real rays `(-∞,-1] ∪ [1,∞)` has its quadratic
radicand in the slit plane. -/
theorem one_sub_sq_mem_slitPlane_of_not_real_large (w : ℂ)
    (h : w.im ≠ 0 ∨ |w.re| < 1) :
    1-w^2 ∈ Complex.slitPlane := by
  by_contra hcut
  obtain ⟨hreal, hlarge⟩ :=
    real_abs_ge_one_of_one_sub_sq_not_mem_slitPlane w hcut
  rcases h with hnonreal | hsmall
  · exact hnonreal hreal
  · exact (not_lt_of_ge hlarge) hsmall

end NLS.ComplexAnalysis
