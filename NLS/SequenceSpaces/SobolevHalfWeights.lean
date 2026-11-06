import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Literal Sobolev half weights and their reciprocals -/
noncomputable section
set_option autoImplicit false
namespace NLS.Weight

theorem sobolev_half_apply (j : ℤ) : sobolev (1/2) j=Real.sqrt (1+|(j : ℝ)|) := by
  rw [sobolev_apply,Real.sqrt_eq_rpow]

theorem sobolev_neg_half_apply (j : ℤ) : sobolev (-1/2) j=(Real.sqrt (1+|(j : ℝ)|))⁻¹ := by
  rw [sobolev_apply,show (-1/2 : ℝ)=-(1/2) by ring,Real.rpow_neg (by positivity),← Real.sqrt_eq_rpow]

theorem sobolev_minus_one_apply (j : ℤ) : sobolev (-1) j=(1+|(j : ℝ)|)⁻¹ := by
  rw [sobolev_apply,Real.rpow_neg_one]

end NLS.Weight
