import NLS.SequenceSpaces.RealCoeff

/-! # Isometric inclusion of real coefficient sequences -/

noncomputable section
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complex inclusion preserves the coefficient norm, also at infinity. -/
theorem norm_complexCLM (a : RealCoeff p) : ‖complexCLM p a‖ = ‖a‖ := by
  apply le_antisymm
  · apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
    intro n
    simp
  · apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
    intro n
    simp

end NLS.RealCoeff
