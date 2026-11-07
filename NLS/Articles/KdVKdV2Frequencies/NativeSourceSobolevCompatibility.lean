import NLS.Articles.KdVKdV2Frequencies.NativeActionNormalization
import NLS.KdV.NativeHillPhysicalSource

/-! Actual normalized source inclusions preserve every raw original
coefficient, including the original real L2 source and its zero mean. -/
noncomputable section
open NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

theorem realNativeSource_sobolev_inclusion
    (s t : ℝ) (hs : 0≤s) (ht : 0≤t) (hst : t≤s) (a : physicalRealDeletedSubmodule) :
    GlobalRoughAbelianForwardData.realNativeSource t ht
      (physicalRealSobolevInclusion (by linarith : t-1≤s-1) a)=
      GlobalRoughAbelianForwardData.realNativeSource s hs a := by
  have h := WeightedCoeff.meanZeroSobolevInclusion_lift (by linarith : t-1≤s-1) a.val
  apply Subtype.ext
  funext j
  rw [GlobalRoughAbelianForwardData.realNativeSource,GlobalRoughAbelianForwardData.realNativeSource,
    periodOneSobolevImageInclusion_apply,periodOneSobolevImageInclusion_apply]
  exact (congrArg (fun q : WeightedCoeff (Weight.sobolev (t-1)) 2 => q.val j) h).trans
    (WeightedCoeff.sobolevInclusion_apply _ _ j)

theorem realNativeSource_two_thirds_inclusion (a : physicalRealDeletedSubmodule) :
    GlobalRoughAbelianForwardData.realNativeSource (2/3) (by norm_num)
      (physicalRealSobolevInclusion (by norm_num : (-1/3:ℝ)≤0) a)=
      GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a := by
  have h := realNativeSource_sobolev_inclusion 1 (2/3) (by norm_num) (by norm_num) (by norm_num) a
  simpa only [sub_self,show (2:ℝ)/3-1= -1/3 by norm_num] using h

theorem realNativeSource_original_l2
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))) :
    GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num)
      ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
        (Weight.sobolev_neg ((0:ℕ):ℝ))).symm q)=nativeHillSource 0 q.val := by
  have h := realNativeSource_original_weighted_coordinates ((0:ℕ):ℝ) (by norm_num) q
  apply Subtype.ext
  funext j
  have hj := congrArg (fun p : PeriodOneHminusOne => p.val j) h
  simpa only [show ((0:ℕ):ℝ)+1=1 by norm_num,WeightedCoeff.sobolevInclusion_apply,
    nativeHillSource_apply] using hj

theorem original_l2_native_source_inclusion
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))) :
    GlobalRoughAbelianForwardData.realNativeSource (2/3) (by norm_num)
      (physicalRealSobolevInclusion (by norm_num : (-1/3:ℝ)≤0)
        ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
          (Weight.sobolev_neg ((0:ℕ):ℝ))).symm q))=nativeHillSource 0 q.val :=
  (realNativeSource_two_thirds_inclusion _).trans (realNativeSource_original_l2 q)

end NLS.Articles.KdVKdV2Frequencies
