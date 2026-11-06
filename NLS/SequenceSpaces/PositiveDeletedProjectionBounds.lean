import NLS.SequenceSpaces.PositiveDeletedProjection

/-! # Contractivity of positive deleted-coordinate projections -/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_positiveDeletedProjection_le (n : ℤ) (a : Coeff p) :
    ‖positiveDeletedProjection p n a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
  intro m
  rw [positiveDeletedProjection_apply]
  split_ifs
  · exact le_rfl
  · exact (norm_zero : ‖(0 : ℂ)‖ = 0).le.trans (norm_nonneg _)

theorem norm_positiveDeletedProjection_le_one (n : ℤ) :
    ‖positiveDeletedProjection p n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simpa only [one_mul] using norm_positiveDeletedProjection_le n a

end NLS.Coeff
