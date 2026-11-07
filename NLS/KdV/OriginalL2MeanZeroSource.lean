import NLS.SequenceSpaces.ComplexMeanZeroWeighted
import NLS.SequenceSpaces.PeriodOneSobolevMiuraInverse

/-! Literal bounded inclusions of the ORIGINAL complex mean-zero L2
space, with EVERY raw coefficient and its inherited original norm. -/
noncomputable section
namespace NLS.KdV

def originalL2MeanZeroNativeInclusion :
    complexMeanZeroWeightedSubmodule (Weight.sobolev 0) →L[ℂ]
      WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 :=
  (WeightedCoeff.sobolevInclusion (by norm_num : (1:ℝ)-1≤0)).comp
    (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)).subtypeL

def originalL2MeanZeroSource :
    complexMeanZeroWeightedSubmodule (Weight.sobolev 0) →L[ℂ] PeriodOneHminusOne :=
  (periodOneSobolevImageInclusion 1 (by norm_num)).comp originalL2MeanZeroNativeInclusion

theorem originalL2MeanZeroNativeInclusion_apply
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (originalL2MeanZeroNativeInclusion q).val j=q.val.val j := by
  change (WeightedCoeff.sobolevInclusion (by norm_num : (1:ℝ)-1≤0) q.val).val j=_
  exact WeightedCoeff.sobolevInclusion_apply (by norm_num : (1:ℝ)-1≤0) q.val j

theorem originalL2MeanZeroSource_apply
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (originalL2MeanZeroSource q).val j=q.val.val j := by
  change (periodOneSobolevImageInclusion 1 (by norm_num) (originalL2MeanZeroNativeInclusion q)).val j=_
  rw [periodOneSobolevImageInclusion_apply,originalL2MeanZeroNativeInclusion_apply]

theorem originalL2MeanZeroSource_zero_coefficient
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    (originalL2MeanZeroSource q).val 0=0 := by
  rw [originalL2MeanZeroSource_apply]
  exact q.property

end NLS.KdV
