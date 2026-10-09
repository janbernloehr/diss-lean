import NLS.SequenceSpaces.NonnegativeActions

/-! # A nonnegative majorant with the exact coefficient norm

Adding a sufficiently large real multiple of the coefficient modulus moves
a real sequence into the nonnegative cone without changing the exponent.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞}

/-- Coordinate norms, viewed as nonnegative real complex coefficients. -/
def coefficientModulus (a : Coeff p) : Coeff p :=
  ⟨fun n => (‖a n‖ : ℂ), by
    apply Memℓp.of_norm
    simpa using (lp.memℓp a).norm⟩

@[simp] theorem coefficientModulus_apply (a : Coeff p) (n : ℤ) :
    coefficientModulus a n = (‖a n‖ : ℂ) := rfl

/-- The modulus lies in the original nonnegative cone. -/
theorem coefficientModulus_nonnegative (a : Coeff p) :
    coefficientModulus a ∈ nonnegativeLocus p := by
  intro n
  simp

variable [Fact (1 ≤ p)]

/-- The modulus preserves the full sequence norm, also at infinite exponent. -/
@[simp] theorem norm_coefficientModulus (a : Coeff p) : ‖coefficientModulus a‖ = ‖a‖ := by
  have hp : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
  apply le_antisymm <;> apply lp.norm_mono hp <;> intro n <;> simp

omit [Fact (1 ≤ p)] in
/-- A real sequence displaced from a nonnegative center becomes nonnegative
along a short affine line past parameter one. -/
theorem add_coefficientModulus_nonnegative {c y : Coeff p}
    (hc : c ∈ nonnegativeLocus p) (hy : y ∈ realLocus p) {t : ℝ} (ht : 1 ≤ t) :
    y+t • coefficientModulus (y-c) ∈ nonnegativeLocus p := by
  intro n
  change ((y n+t • (‖(y-c) n‖ : ℂ)).im = 0) ∧ 0 ≤ (y n+t • (‖(y-c) n‖ : ℂ)).re
  constructor
  · simp [hy n]
  · simp only [Complex.add_re,Complex.smul_re,Complex.ofReal_re,smul_eq_mul]
    have hb := (abs_le.mp (Complex.abs_re_le_norm ((y-c) n))).1
    change -‖(y-c) n‖ ≤ (y n-c n).re at hb
    rw [Complex.sub_re] at hb
    have hn := (hc n).2
    have hm := mul_nonneg (sub_nonneg.mpr ht) (norm_nonneg ((y-c) n))
    nlinarith

end NLS.Coeff
