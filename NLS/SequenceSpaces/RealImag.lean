import NLS.SequenceSpaces.Truncation

/-!
# Real and imaginary components of full complex sequences

Pointwise conjugation preserves `ℓᵖ`. Its real and imaginary
components are real sequences in the same space and reconstruct the
original direction.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def realPart (h : Coeff p) : Coeff p := (1/2 : ℂ) • (h + star h)

def imagPart (h : Coeff p) : Coeff p := (-I/2 : ℂ) • (h - star h)

theorem realPart_apply (h : Coeff p) (j : ℤ) :
    realPart h j = ((h j).re : ℂ) := by
  simp only [realPart, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.coeFn_add, Pi.add_apply, lp.star_apply]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.add_re]
    ring
  · simp [Complex.mul_im, Complex.add_im]

theorem imagPart_apply (h : Coeff p) (j : ℤ) :
    imagPart h j = ((h j).im : ℂ) := by
  simp only [imagPart, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.coeFn_sub, Pi.sub_apply, lp.star_apply]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.sub_re]
    ring
  · simp [Complex.mul_im, Complex.sub_im]

theorem realPart_im_eq_zero (h : Coeff p) (j : ℤ) :
    (realPart h j).im = 0 := by rw [realPart_apply]; simp

theorem imagPart_im_eq_zero (h : Coeff p) (j : ℤ) :
    (imagPart h j).im = 0 := by rw [imagPart_apply]; simp

theorem realPart_add_I_imagPart (h : Coeff p) :
    realPart h + I • imagPart h = h := by
  ext j
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, realPart_apply, imagPart_apply]
  calc
    _ = ((h j).re : ℂ) + ((h j).im : ℂ) * I := by ring
    _ = h j := Complex.re_add_im (h j)

end NLS.Coeff
