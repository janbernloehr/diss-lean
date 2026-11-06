import NLS.SequenceSpaces.MeanZeroSobolevInclusion

/-! # Exact identities when the native Sobolev exponents agree -/
noncomputable section
set_option autoImplicit false
namespace NLS.WeightedCoeff

/-- Equal-order inclusion is literally the identity in the common
normalized mean-zero coefficient space; no dependent-space casts occur. -/
theorem meanZeroSobolevInclusion_self (s : ℝ) (h : s ≤ s) :
    meanZeroSobolevInclusion h = ContinuousLinearMap.id ℂ (DeletedCoeff 2 0) := by
  ext a j
  by_cases hj : j = 0
  · subst j
    exact (meanZeroSobolevInclusion h a).property.trans a.property.symm
  · change (meanZeroWeightedProjectionCLM (Weight.sobolev s)
      (sobolevInclusion h (meanZeroWeightedLiftCLM (Weight.sobolev s) a))).val j = a.val j
    rw [meanZeroWeightedProjection_apply_other _ _ j hj,sobolevInclusion_apply,
      meanZeroWeightedLift_apply,mul_div_cancel₀ _ (Weight.complex_ne_zero _ _)]

end NLS.WeightedCoeff
