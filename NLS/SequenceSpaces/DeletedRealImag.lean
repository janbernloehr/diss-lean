import NLS.SequenceSpaces.DeletedCoordinate

/-!
# Real and imaginary parts of a deleted complex sequence

Pointwise conjugation preserves the omitted-coordinate subspace. The
usual real and imaginary parts therefore belong to the same deleted
`ℓᵖ` space and reconstruct every complex direction.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS

namespace DeletedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {n : ℤ}

/-- Pointwise conjugation on the deleted sequence space. -/
def conj (h : DeletedCoeff p n) : DeletedCoeff p n :=
  ⟨star (h : Coeff p), by
    have hn : (h : Coeff p) n = 0 := h.property
    change (star (h : Coeff p)) n = 0
    rw [lp.star_apply]
    simp [hn]⟩

@[simp] theorem conj_apply (h : DeletedCoeff p n) (j : ℤ) :
    ((conj h : DeletedCoeff p n) : Coeff p) j =
      star ((h : Coeff p) j) := by
  rfl

@[simp] theorem conj_zero : conj (0 : DeletedCoeff p n) = 0 := by
  apply Subtype.ext
  ext j
  simp

/-- The real-coordinate component of a deleted direction. -/
def realPart (h : DeletedCoeff p n) : DeletedCoeff p n :=
  (1/2 : ℂ) • (h + conj h)

/-- The imaginary-coordinate component of a deleted direction. -/
def imagPart (h : DeletedCoeff p n) : DeletedCoeff p n :=
  (-I/2 : ℂ) • (h - conj h)

theorem realPart_apply (h : DeletedCoeff p n) (j : ℤ) :
    ((realPart h : DeletedCoeff p n) : Coeff p) j =
      (((h : Coeff p) j).re : ℂ) := by
  simp only [realPart, Submodule.coe_smul, Submodule.coe_add,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add,
    Pi.add_apply, conj_apply]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.add_re]
    ring
  · simp [Complex.mul_im, Complex.add_im]

theorem imagPart_apply (h : DeletedCoeff p n) (j : ℤ) :
    ((imagPart h : DeletedCoeff p n) : Coeff p) j =
      (((h : Coeff p) j).im : ℂ) := by
  simp only [imagPart, Submodule.coe_smul, Submodule.coe_sub,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sub,
    Pi.sub_apply, conj_apply]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.sub_re]
    ring
  · simp [Complex.mul_im, Complex.sub_im]

theorem realPart_im_eq_zero (h : DeletedCoeff p n) (j : ℤ) :
    (((realPart h : DeletedCoeff p n) : Coeff p) j).im = 0 := by
  rw [realPart_apply]
  simp

theorem imagPart_im_eq_zero (h : DeletedCoeff p n) (j : ℤ) :
    (((imagPart h : DeletedCoeff p n) : Coeff p) j).im = 0 := by
  rw [imagPart_apply]
  simp

theorem realPart_add_I_imagPart (h : DeletedCoeff p n) :
    realPart h + I • imagPart h = h := by
  apply Subtype.ext
  ext j
  simp only [Submodule.coe_add, Submodule.coe_smul, lp.coeFn_add,
    lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    realPart_apply, imagPart_apply]
  calc
    _ = (((h : Coeff p) j).re : ℂ) +
        (((h : Coeff p) j).im : ℂ) * I := by ring
    _ = (h : Coeff p) j := Complex.re_add_im ((h : Coeff p) j)

end DeletedCoeff
end NLS
