import NLS.SequenceSpaces.MeanZeroWeightedCoordinates

/-! # Exact injectivity of the actual weak projection on zero-mean coefficients -/
noncomputable section
set_option autoImplicit false
namespace NLS.WeightedCoeff

theorem meanZeroWeightedProjection_injective_of_zero
    (w : Weight) (a b : WeightedCoeff w 2) (ha : a.val 0=0) (hb : b.val 0=0)
    (he : meanZeroWeightedProjectionCLM w a=meanZeroWeightedProjectionCLM w b) : a=b := by
  have h := congrArg (meanZeroWeightedLiftCLM w) he
  rwa [meanZeroWeightedLift_projection w a ha,meanZeroWeightedLift_projection w b hb] at h

end NLS.WeightedCoeff
