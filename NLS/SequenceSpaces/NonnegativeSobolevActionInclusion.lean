import NLS.SequenceSpaces.SobolevDerivative
import NLS.SequenceSpaces.WeightedPositiveActionDerivatives

/-! Nonnegative Sobolev order includes into the ORIGINAL unweighted
coefficient norm, preserving every raw action and every zero slot. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def nonnegativeSobolevToCoeffCLM (α : ℝ) (hα : 0≤α) :
    WeightedCoeff (Weight.sobolev α) p →L[ℂ] Coeff p :=
  (weightIsometry (Weight.sobolev 0) p).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sobolevInclusion hα)

@[simp] theorem nonnegativeSobolevToCoeffCLM_apply (α : ℝ) (hα : 0≤α)
    (a : WeightedCoeff (Weight.sobolev α) p) (j : ℤ) :
    nonnegativeSobolevToCoeffCLM α hα a j=a.val j := by
  change (Weight.sobolev 0 j : ℂ)*(sobolevInclusion hα a).val j=_
  rw [sobolevInclusion_apply]
  norm_num [Weight.sobolev_apply]

theorem nonnegativeSobolevToCoeffCLM_nonnegative (α : ℝ) (hα : 0≤α)
    (a : WeightedCoeff (Weight.sobolev α) p) (ha : a∈nonnegativeLocus (Weight.sobolev α) p) :
    nonnegativeSobolevToCoeffCLM α hα a∈Coeff.nonnegativeLocus p := by
  intro j
  simpa only [nonnegativeSobolevToCoeffCLM_apply] using ha j

end NLS.WeightedCoeff
