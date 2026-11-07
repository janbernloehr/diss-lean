import NLS.Articles.KdVKdV2Frequencies.Theorem12StrongEndpoint
import NLS.Articles.KdVKdV2Frequencies.Theorem12WeakEndpoint

/-! Actual native actions in every original lower Sobolev action norm.
All raw coefficients and their weak normalization are unchanged. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def nativeSobolevRawActions (D : GlobalRoughAbelianForwardData) (α : ℝ) (hα : α≤3)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    WeightedCoeff (Weight.sobolev α) 1 :=
  WeightedCoeff.sobolevInclusion hα (D.nativeSourceActionSequence 1 3 (by norm_num) q)

@[simp] theorem nativeSobolevRawActions_coefficient (D : GlobalRoughAbelianForwardData)
    (α : ℝ) (hα : α≤3)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (j : ℤ) :
    (D.nativeSobolevRawActions α hα q).val j=(D.nativeSourceActionSequence 1 3 (by norm_num) q).val j :=
  WeightedCoeff.sobolevInclusion_apply _ _ _

theorem nativeSobolevRawActions_positive (D : GlobalRoughAbelianForwardData)
    (α : ℝ) (hα : α≤3)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    D.nativeSobolevRawActions α hα q∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1 := by
  constructor
  · intro j
    simpa only [nativeSobolevRawActions_coefficient,←nativeRawKdVActions_coefficient] using
      D.nativeRawKdVActions_nonnegative q j
  · intro j hj
    rw [nativeSobolevRawActions_coefficient,←nativeRawKdVActions_coefficient]
    exact D.nativeRawKdVActions_nonpositive q j hj

theorem nativeSobolevRawActions_weak (D : GlobalRoughAbelianForwardData)
    (α : ℝ) (hα : α≤3) (hαw : -1≤α)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    weakActionNormalization (WeightedCoeff.sobolevInclusion hαw (D.nativeSobolevRawActions α hα q))=
      D.nativeWeakActionSequence 1 q := by
  ext j
  change (Weight.sobolev (-1) j : ℂ)*
    (WeightedCoeff.sobolevInclusion hαw (D.nativeSobolevRawActions α hα q)).val j=_
  rw [WeightedCoeff.sobolevInclusion_apply,nativeSobolevRawActions_coefficient,
    D.nativeWeakActionSequence_apply 1 3 (by norm_num) q]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
