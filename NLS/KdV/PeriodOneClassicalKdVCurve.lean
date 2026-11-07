import NLS.SequenceSpaces.PeriodOneKdVNativeVector
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedExponent

/-! # Actual strong classical KdV curves on the unit circle

The trajectory is continuous in H4 and has its time derivative in H1,
with the literal conservative KdV vector. The definition contains no
Birkhoff coordinates or spectral evolution assumptions.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.KdV

def IsPeriodOneClassicalKdVCurve
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2) : Prop :=
  Continuous u ∧ ∀ t : ℝ,
    HasDerivAt (fun r : ℝ => WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4) (u r).val)
      (periodOneKdVNativeVector (u t).val) t

end NLS.KdV
