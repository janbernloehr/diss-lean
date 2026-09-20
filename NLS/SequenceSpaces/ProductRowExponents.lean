import NLS.SequenceSpaces.YoungExponents
import NLS.SequenceSpaces.DoublingProduct
import Mathlib.Tactic.NormNum

/-!
# Exponents for quadratic reciprocal-row errors

The absolute reciprocal row is placed in the doubled input exponent by Young.
Squaring then returns to the original exponent by Hölder. Its kernel exponent
is the conjugate of the doubled exponent, strictly above one at finite inputs.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Hölder multiplication from twice an exponent back to that exponent. -/
theorem holderTriple_double (p : ℝ≥0∞) : (2*p).HolderTriple (2*p) p := by
  rw [ENNReal.holderTriple_iff, ENNReal.mul_inv (by left; norm_num) (by left; norm_num), ← add_mul]
  rw [ENNReal.inv_two_add_inv_two, one_mul]

/-- Doubling preserves the Banach lower bound. -/
theorem one_le_double_exponent {p : ℝ≥0∞} (hp : 1 ≤ p) : 1 ≤ 2*p := by
  calc
    1 ≤ p := hp
    _ ≤ 2*p := by simpa [mul_comm] using mul_le_mul_right (by norm_num : (1 : ℝ≥0∞) ≤ 2) p

/-- A doubled exponent and its conjugate give the required Young relation. -/
theorem youngRelation_double_conjugate (p : ℝ≥0∞) [Fact (1 ≤ p)] : YoungRelation p (2*p).conjExponent (2*p) := by
  let : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩
  let : (2*p).HolderTriple (2*p) p := holderTriple_double p
  rw [YoungRelation, ENNReal.HolderTriple.inv_eq (2*p) (2*p) p, add_assoc,
    ENNReal.HolderConjugate.inv_add_inv_eq_one, add_comm]

/-- The reciprocal kernel exponent is strictly above one for each finite Banach input. -/
theorem one_lt_double_conjugate {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) : 1 < (2*p).conjExponent := by
  let : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩
  exact (ENNReal.HolderConjugate.lt_top_iff_one_lt (2*p) (2*p).conjExponent).mp
    (ENNReal.mul_ne_top (by norm_num) hp).lt_top

end NLS
