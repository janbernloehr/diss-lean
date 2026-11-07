import NLS.KdV.HillSpectralCoreSequence
import NLS.KdV.HillMeanZeroIntrinsicCompact

/-! The actual spectral-core reduction on the exact complex mean-zero
source and signed minus-half Sobolev zero-mode target. Both the on-index
derivative difference and the combined native remainder are compact. -/
noncomputable section
open Set NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

def physicalMeanZeroSpectralCoreMap (P : HillProductEquationPatch) (q : HillMeanZeroSource) :
    HillSignedComplexTarget :=
  WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2)) (P.physicalSpectralCoreMap q.val)

theorem physicalMeanZeroSpectralCoreMap_coe (P : HillProductEquationPatch) (q : HillMeanZeroSource) :
    (P.physicalMeanZeroSpectralCoreMap q).val=P.physicalSpectralCoreMap q.val :=
  WeightedCoeff.zeroModeProjection_coe _ _ (P.physicalSpectralCoreMap_zero_mode _)

theorem analytic_physicalMeanZeroSpectralCoreMap (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) :
    AnalyticOnNhd ℂ P.physicalMeanZeroSpectralCoreMap
      {q : HillMeanZeroSource | q.val ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain} := by
  intro q hq
  exact ((WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))).analyticAt _).comp
    ((P.analytic_physicalSpectralCoreMap H q.val hq).comp
      ((WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.analyticAt q))

theorem fderiv_physicalMeanZeroSpectralCoreMap_eq_comp (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : HillMeanZeroSource) (hq : q.val ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) :
    fderiv ℂ P.physicalMeanZeroSpectralCoreMap q =
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).comp
        ((fderiv ℂ P.physicalSpectralCoreMap q.val).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) := by
  exact ((WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).hasFDerivAt.comp q
    ((P.analytic_physicalSpectralCoreMap H q.val hq).differentiableAt.hasFDerivAt.comp q
      (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.hasFDerivAt)).fderiv

theorem isCompactOperator_physicalMeanZeroOnIndexJacobianDifference (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : HillMeanZeroSource) (hq : q.val ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) :
    IsCompactOperator (fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q-fderiv ℂ P.physicalMeanZeroSpectralCoreMap q) := by
  have he : fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q-fderiv ℂ P.physicalMeanZeroSpectralCoreMap q =
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).comp
        ((fderiv ℂ hillHminusIntrinsicDiagonalMap q.val-fderiv ℂ P.physicalSpectralCoreMap q.val).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) := by
    apply ContinuousLinearMap.ext
    intro h
    rw [fderiv_hillMeanZeroIntrinsicDiagonalMap_eq_comp q hq.2,P.fderiv_physicalMeanZeroSpectralCoreMap_eq_comp H q hq]
    simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub]
  rw [he]
  exact ((P.isCompactOperator_physicalOnIndexJacobianDifference H q.val hq.1 hq.2).comp_clm
    (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL).clm_comp
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2)))

def physicalMeanZeroSpectralCoreRemainder (P : HillProductEquationPatch) (q : HillMeanZeroSource) :
    HillMeanZeroSource →L[ℂ] HillSignedComplexTarget :=
  fderiv ℂ hillMeanZeroComplexMap q-
    (WeightedCoeff.zeroModeExponentialSymbolEquiv (Weight.signedSobolev (-1/2))
      (hillHminusSignedOffIndexExponent q.val)).toContinuousLinearMap.comp
        (fderiv ℂ P.physicalMeanZeroSpectralCoreMap q)

theorem isCompactOperator_physicalMeanZeroSpectralCoreRemainder (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : HillMeanZeroSource) (hq : q.val ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) :
    IsCompactOperator (P.physicalMeanZeroSpectralCoreRemainder q) := by
  let M := (WeightedCoeff.zeroModeExponentialSymbolEquiv (p := 2) (Weight.signedSobolev (-1/2))
    (hillHminusSignedOffIndexExponent q.val)).toContinuousLinearMap
  have he : P.physicalMeanZeroSpectralCoreRemainder q = hillMeanZeroIntrinsicJacobianRemainder q+
      M.comp (fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q-fderiv ℂ P.physicalMeanZeroSpectralCoreMap q) := by
    apply ContinuousLinearMap.ext
    intro h
    simp only [physicalMeanZeroSpectralCoreRemainder,hillMeanZeroIntrinsicJacobianRemainder,
      sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
    change (fderiv ℂ hillMeanZeroComplexMap q) h-M ((fderiv ℂ P.physicalMeanZeroSpectralCoreMap q) h) =
      (fderiv ℂ hillMeanZeroComplexMap q) h-M ((fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q) h)+
        (M ((fderiv ℂ hillMeanZeroIntrinsicDiagonalMap q) h)-M ((fderiv ℂ P.physicalMeanZeroSpectralCoreMap q) h))
    abel
  rw [he]
  exact (isCompactOperator_hillMeanZeroIntrinsicJacobianRemainder q hq.2).add
    ((P.isCompactOperator_physicalMeanZeroOnIndexJacobianDifference H q hq).clm_comp M)

end NLS.KdV.HillProductEquationPatch
