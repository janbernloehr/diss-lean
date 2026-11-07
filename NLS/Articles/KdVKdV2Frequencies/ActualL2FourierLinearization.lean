import NLS.KdV.OriginalL2MeanZeroSource
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianOrigin

/-! The ACTUAL differential of the SAME global physical map, pulled
through the literal original mean-zero L2 inclusion, is EXACTLY the paper's
weighted Fourier transform at EVERY signed coefficient. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def originalL2Fourier (D : GlobalRoughAbelianForwardData) :
    complexMeanZeroWeightedSubmodule (Weight.sobolev 0) →L[ℂ]
      WeightedCoeff (Weight.sobolev (-1/2)) 2 :=
  (fderiv ℂ D.signed 0).comp originalL2MeanZeroSource

theorem originalL2Fourier_apply (D : GlobalRoughAbelianForwardData)
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (D.originalL2Fourier q).val j=
      (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j := by
  have h := D.signed_fourier_differential (originalL2MeanZeroSource q)
    (originalL2MeanZeroSource_zero_coefficient q) j
  simpa only [originalL2Fourier,ContinuousLinearMap.comp_apply,originalL2MeanZeroSource_apply] using h

theorem hasFDerivAt_original_l2_signed_at_zero (D : GlobalRoughAbelianForwardData) :
    HasFDerivAt (fun q => D.signed (originalL2MeanZeroSource q)) D.originalL2Fourier 0 := by
  have h : HasFDerivAt D.signed (fderiv ℂ D.signed 0) (originalL2MeanZeroSource 0) := by
    simpa only [map_zero] using
      (D.signed_analytic 0 (D.real_mem_domain 0 (by intro j;simp))).differentiableAt.hasFDerivAt
  exact h.comp 0 originalL2MeanZeroSource.hasFDerivAt

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
