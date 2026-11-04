import NLS.KdV.HillIntrinsicDiagonalSequence

/-! The actual intrinsic diagonal sequence on the exact mean-zero
source and target. The normalized amplitude changes its Jacobian by a
compact operator; together with the off-index phase this reduces the
native inverse problem to this fixed-normalization intrinsic map. -/
noncomputable section
open Set
namespace NLS.KdV

def hillMeanZeroIntrinsicDiagonalMap (q : HillMeanZeroSource) : HillSignedComplexTarget :=
  WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))
    (hillHminusIntrinsicDiagonalMap q.val)

theorem hillMeanZeroIntrinsicDiagonalMap_coe (q : HillMeanZeroSource) :
    (hillMeanZeroIntrinsicDiagonalMap q).val=hillHminusIntrinsicDiagonalMap q.val :=
  WeightedCoeff.zeroModeProjection_coe _ _ (hillHminusIntrinsicDiagonalMap_zero_mode _)

theorem analyticOnNhd_hillMeanZeroIntrinsicDiagonalMap :
    AnalyticOnNhd ℂ hillMeanZeroIntrinsicDiagonalMap hillMeanZeroComplexDomain := by
  intro q hq
  exact ((WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))).analyticAt _).comp
    ((analyticOnNhd_hillHminusIntrinsicDiagonalMap _ hq).comp
      ((WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.analyticAt q))

theorem fderiv_hillMeanZeroIntrinsicDiagonalMap_eq_comp (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) :
    fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q=
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).comp
        ((fderiv ℂ hillHminusIntrinsicDiagonalMap q.val).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) := by
  exact ((WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).hasFDerivAt.comp q
    ((analyticOnNhd_hillHminusIntrinsicDiagonalMap q.val hq).differentiableAt.hasFDerivAt.comp q
      (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.hasFDerivAt)).fderiv

theorem isCompactOperator_hillMeanZeroAmplitudeJacobianDifference (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) :
    IsCompactOperator (fderiv ℂ hillMeanZeroDiagonalMap q-fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q) := by
  have he : fderiv ℂ hillMeanZeroDiagonalMap q-fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q =
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).comp
        ((fderiv ℂ hillHminusNativeDiagonalMap q.val-fderiv ℂ hillHminusIntrinsicDiagonalMap q.val).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) := by
    apply ContinuousLinearMap.ext
    intro h
    rw [fderiv_hillMeanZeroDiagonalMap_eq_comp q hq,fderiv_hillMeanZeroIntrinsicDiagonalMap_eq_comp q hq]
    simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub]
  rw [he]
  exact ((isCompactOperator_hillHminusAmplitudeJacobianDifference q.val hq).comp_clm
    (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL).clm_comp
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2)))

def hillMeanZeroIntrinsicJacobianRemainder (q : HillMeanZeroSource) :
    HillMeanZeroSource →L[ℂ] HillSignedComplexTarget :=
  fderiv ℂ hillMeanZeroComplexMap q-
    (WeightedCoeff.zeroModeExponentialSymbolEquiv (Weight.signedSobolev (-1/2))
      (hillHminusSignedOffIndexExponent q.val)).toContinuousLinearMap.comp
        (fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q)

theorem isCompactOperator_hillMeanZeroIntrinsicJacobianRemainder (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) :
    IsCompactOperator (hillMeanZeroIntrinsicJacobianRemainder q) := by
  let M := (WeightedCoeff.zeroModeExponentialSymbolEquiv (p := 2) (Weight.signedSobolev (-1/2))
    (hillHminusSignedOffIndexExponent q.val)).toContinuousLinearMap
  have he : hillMeanZeroIntrinsicJacobianRemainder q = hillMeanZeroOffIndexJacobianRemainder q+
      M.comp (fderiv ℂ hillMeanZeroDiagonalMap q-fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q) := by
    apply ContinuousLinearMap.ext
    intro h
    simp only [hillMeanZeroIntrinsicJacobianRemainder,hillMeanZeroOffIndexJacobianRemainder,
      sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
    change (fderiv ℂ hillMeanZeroComplexMap q) h-M ((fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q) h) =
      (fderiv ℂ hillMeanZeroComplexMap q) h-M ((fderiv ℂ hillMeanZeroDiagonalMap q) h)+
        (M ((fderiv ℂ hillMeanZeroDiagonalMap q) h)-M ((fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q) h))
    abel
  rw [he]
  exact (isCompactOperator_hillMeanZeroOffIndexJacobianRemainder q hq).add
    ((isCompactOperator_hillMeanZeroAmplitudeJacobianDifference q hq).clm_comp M)

end NLS.KdV
