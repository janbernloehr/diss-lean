import NLS.KdV.HillNativeZeroGardner

/-! The actual derivative restricted to the exact complex mean-zero
source and signed zero-mode target, at GENERAL points of its native
domain. Its raw coordinates agree with the full ambient derivative. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV

theorem fderiv_hillMeanZeroComplexMap_eq_comp (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) :
    fderiv ℂ hillMeanZeroComplexMap q=
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).comp
        ((fderiv ℂ hillHminusNativeComplexMap q.val).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) := by
  have hi := (analyticOnNhd_hillHminusNativeComplexMap q.val hq).differentiableAt.hasFDerivAt
  have hd := ((WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).hasFDerivAt.comp q
    (hi.comp q (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.hasFDerivAt)).fderiv
  exact hd

theorem fderiv_hillMeanZeroComplexMap_coe (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) (h : HillMeanZeroSource) :
    ((fderiv ℂ hillMeanZeroComplexMap q) h).val=
      (fderiv ℂ hillHminusNativeComplexMap q.val) h.val := by
  rw [fderiv_hillMeanZeroComplexMap_eq_comp q hq]
  change (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))
    ((fderiv ℂ hillHminusNativeComplexMap q.val) h.val) : WeightedCoeff (Weight.signedSobolev (-1/2)) 2)=_
  apply WeightedCoeff.zeroModeProjection_coe
  rw [← fderiv_hillHminusNativeCoordinate 0 q.val hq h.val,hillHminusNativeCoordinate_zero_mode,
    (hasFDerivAt_const (0:ℂ) q.val).fderiv]
  exact zero_apply h.val

theorem fderiv_hillMeanZeroComplexMap_coordinate (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) (h : HillMeanZeroSource) (k : ℤ) :
    ((fderiv ℂ hillMeanZeroComplexMap q) h).val.val k=
      (fderiv ℂ (hillHminusNativeCoordinate k) q.val) h.val := by
  rw [fderiv_hillMeanZeroComplexMap_coe q hq h]
  exact (fderiv_hillHminusNativeCoordinate k q.val hq h.val).symm

end NLS.KdV
