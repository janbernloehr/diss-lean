import NLS.SequenceSpaces.DeletedCoordinate
import NLS.SequenceSpaces.ExponentEmbedding

/-! # Exponent inclusion for deleted-coordinate sequences -/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Exponent inclusion preserves the zero at the deleted coordinate. -/
def deletedExponentInclusion (hpq : p ≤ q) (n : ℤ) : DeletedCoeff p n →L[ℂ] DeletedCoeff q n :=
  ((exponentInclusion hpq).comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).codRestrict
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).ker (fun a => a.property)

@[simp] theorem coe_deletedExponentInclusion (hpq : p ≤ q) (n : ℤ) (a : DeletedCoeff p n) :
    (deletedExponentInclusion hpq n a : Coeff q) = exponentInclusion hpq (a : Coeff p) := rfl

@[simp] theorem deletedExponentInclusion_apply (hpq : p ≤ q) (n : ℤ) (a : DeletedCoeff p n) (m : ℤ) :
    (deletedExponentInclusion hpq n a : Coeff q) m = (a : Coeff p) m := rfl

theorem norm_deletedExponentInclusion_le (hpq : p ≤ q) (n : ℤ) (a : DeletedCoeff p n) :
    ‖deletedExponentInclusion hpq n a‖ ≤ ‖a‖ := norm_exponentInclusion_le hpq (a : Coeff p)

end NLS.Coeff
