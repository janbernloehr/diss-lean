import NLS.SequenceSpaces.PositiveDeletedSpace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.Coeff



/-- Projection to the actual positive deleted coefficient space is contractive. -/
theorem norm_positiveDeletedProjectionTo_le (p : ℝ≥0∞) [Fact (1≤p)] (n : ℤ) (a : Coeff p) :
    ‖positiveDeletedProjectionTo p n a‖≤‖a‖ := by
  change ‖positiveDeletedProjection p n a‖≤‖a‖
  apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1≤p)))
  intro m
  rw [positiveDeletedProjection_apply]
  split_ifs
  · exact le_rfl
  · simp only [norm_zero]
    exact norm_nonneg _

theorem norm_positiveDeletedProjectionTo_le_one (p : ℝ≥0∞) [Fact (1≤p)] (n : ℤ) :
    ‖positiveDeletedProjectionTo p n‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  simpa only [one_mul] using norm_positiveDeletedProjectionTo_le p n a

end NLS.Coeff
