import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.ConjugateDuality

/-!
# Exponents in the general Young inequality

The source relation is `1 + 1/r = 1/p + 1/q`, with infinity interpreted by
reciprocal zero. It implies that both inputs embed into the output exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- The exact exponent relation in Appendix B, Lemma B.2. -/
def YoungRelation (p q r : ℝ≥0∞) : Prop := 1 + r⁻¹ = p⁻¹ + q⁻¹

namespace YoungRelation
variable {p q r : ℝ≥0∞}

theorem symm (h : YoungRelation p q r) : YoungRelation q p r := by
  simpa only [YoungRelation, add_comm] using h

/-- Each input exponent is at most the output exponent. -/
theorem left_le [Fact (1 ≤ q)] (h : YoungRelation p q r) : p ≤ r := by
  apply ENNReal.inv_le_inv.mp
  apply ENNReal.le_of_add_le_add_left (a := 1) (by simp)
  calc
    1 + r⁻¹ = p⁻¹ + q⁻¹ := h
    _ ≤ p⁻¹ + 1 := by
      apply add_le_add le_rfl
      simpa only [inv_one] using ENNReal.inv_le_inv.mpr (show 1 ≤ q from Fact.out)
    _ = 1 + p⁻¹ := add_comm _ _

theorem right_le [Fact (1 ≤ p)] (h : YoungRelation p q r) : q ≤ r := h.symm.left_le

/-- Input exponents are finite whenever the output exponent is finite. -/
theorem left_ne_top [Fact (1 ≤ q)] (h : YoungRelation p q r) (hr : r ≠ ⊤) : p ≠ ⊤ :=
  ne_top_of_le_ne_top hr h.left_le

theorem right_ne_top [Fact (1 ≤ p)] (h : YoungRelation p q r) (hr : r ≠ ⊤) : q ≠ ⊤ :=
  ne_top_of_le_ne_top hr h.right_le

/-- At an infinity output, the inputs are Hölder conjugate. -/
theorem holderConjugate (h : YoungRelation p q ⊤) : p.HolderConjugate q :=
  ⟨by simpa only [ENNReal.inv_top, add_zero, inv_one] using (Eq.symm h)⟩

/-- Every admissible second input embeds into the Hölder conjugate of the first. -/
theorem right_le_conjExponent [Fact (1 ≤ p)] (h : YoungRelation p q r) : q ≤ p.conjExponent := by
  apply ENNReal.inv_le_inv.mp
  apply ENNReal.le_of_add_le_add_left
    (a := p⁻¹) (by simp [ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))])
  rw [ENNReal.HolderConjugate.inv_add_inv_eq_one p p.conjExponent]
  exact (le_add_of_nonneg_right (show 0 ≤ r⁻¹ from bot_le)).trans_eq h

/-- The corresponding relation for real exponent reciprocals. -/
theorem toReal [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] (h : YoungRelation p q r) :
    1 + 1 / r.toReal = 1 / p.toReal + 1 / q.toReal := by
  have hp : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
  have hq : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
  have hr : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
  have he := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (a := 1) (b := r⁻¹) (by simp) (by simpa using hr),
    ENNReal.toReal_add (a := p⁻¹) (b := q⁻¹) (by simpa using hp) (by simpa using hq)] at he
  simpa only [ENNReal.toReal_one, ENNReal.toReal_inv, one_div] using he

/-- Combining the output dual exponent with the Young relation gives the trilinear relation. -/
theorem dual_toReal {t : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [r.HolderConjugate t] (h : YoungRelation p q r) :
    1 / p.toReal + 1 / q.toReal + 1 / t.toReal = 2 := by
  have hr : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
  have ht : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le (ENNReal.HolderConjugate.one_le t r))
  have hc := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one r t)
  simp only [ENNReal.toReal_add (a := r⁻¹) (b := t⁻¹) (by simpa using hr) (by simpa using ht),
    ENNReal.toReal_inv, ENNReal.toReal_one] at hc
  have hy := h.toReal
  simp only [one_div] at hy ⊢
  linarith

end YoungRelation
end NLS
