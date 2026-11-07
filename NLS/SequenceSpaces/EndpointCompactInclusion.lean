import NLS.SequenceSpaces.WeightedWeakStarLowerTopology
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Compact lower-norm inclusion of the full endpoint Banach space

The domain carries its original strong infinity norm. Banach--Alaoglu and
the bounded-set lower-norm topology imply norm compactness of the included
unit ball. No finite-exponent source space or vanishing-tail hypothesis on
an endpoint vector is imposed.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The strong endpoint unit ball has compact image in every admissible lower norm space. -/
theorem isCompact_endpointLowerInclusion_closedBall (r t R : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal) :
    IsCompact (endpointLowerInclusion (-r) t hp h '' closedBall 0 R) := by
  have hc := (isCompact_weakStar_iff_bounded_lower_compact r t hp h
    (weakStarBall r R)).mp (isCompact_weakStarBall r R) |>.2
  rw [← image_wienerDualRealization_closedBall r R, ← image_comp] at hc
  have he : lowerWeakStarRealization r t hp h ∘ wienerDualRealization r =
      endpointLowerInclusion (-r) t hp h := by
    funext a
    simp only [Function.comp_def, lowerWeakStarRealization,
      weakStarCoeff_wienerDualRealization]
  rw [he] at hc
  exact hc

/-- The inclusion is compact as an operator on the actual strong endpoint Banach space. -/
theorem isCompactOperator_endpointLowerInclusion (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal) : IsCompactOperator (endpointLowerInclusion (-r) t hp h) := by
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (endpointLowerInclusion (-r) t hp h).toLinearMap (by norm_num : (0:ℝ) < 1)).mpr
  exact ⟨_, isCompact_endpointLowerInclusion_closedBall r t 1 hp h, Subset.rfl⟩

end NLS.WeightedCoeff
