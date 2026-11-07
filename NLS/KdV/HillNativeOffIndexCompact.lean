import NLS.KdV.HillNativeDiagonalGauge
import NLS.KdV.HillNativeMeanZeroDerivative
import NLS.SequenceSpaces.ZeroModeExponentialSymbol

/-! The actual infinite off-index phase contributes a compact operator
to the native Jacobian, on the full complex native domain. The same
decomposition holds on the exact mean-zero source and target. No
compactness of the remaining diagonal Jacobian is assumed or asserted. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV

def hillHminusOffIndexJacobianRemainder (q : PeriodOneHminusOne) :
    PeriodOneHminusOne →L[ℂ] WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  fderiv ℂ hillHminusNativeComplexMap q -
    (WeightedCoeff.exponentialSymbolEquiv (Weight.signedSobolev (-1/2))
      (hillHminusSignedOffIndexExponent q)).toContinuousLinearMap.comp
        (fderiv ℂ hillHminusNativeDiagonalMap q)

theorem hillHminusOffIndexJacobianRemainder_eq (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    hillHminusOffIndexJacobianRemainder q =
      ((WeightedCoeff.boundedSymbolBilinear (Weight.signedSobolev (-1/2))).flip
        (hillHminusNativeComplexMap q)).comp (fderiv ℂ hillHminusSignedOffIndexExponent q) :=
  WeightedCoeff.fderiv_removeExponentialSymbol_remainder _ _ _ q
    (analyticOnNhd_hillHminusSignedOffIndexExponent q
      (hillHminusActionAngleNativeDomain_subset_offIndexBounded hq))
    (analyticOnNhd_hillHminusNativeComplexMap q hq)

theorem hillHminusOffIndexJacobianRemainder_coordinate (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (h : PeriodOneHminusOne) (k : ℤ) :
    (hillHminusOffIndexJacobianRemainder q h).val k =
      ((fderiv ℂ hillHminusSignedOffIndexExponent q) h k)*(hillHminusNativeComplexMap q).val k := by
  rw [hillHminusOffIndexJacobianRemainder_eq q hq]
  rfl

theorem isCompactOperator_hillHminusOffIndexJacobianRemainder (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    IsCompactOperator (hillHminusOffIndexJacobianRemainder q) :=
  WeightedCoeff.isCompactOperator_removeExponentialSymbol_remainder _ (by norm_num) _ _ q
    (analyticOnNhd_hillHminusSignedOffIndexExponent q
      (hillHminusActionAngleNativeDomain_subset_offIndexBounded hq))
    (analyticOnNhd_hillHminusNativeComplexMap q hq)

def hillMeanZeroDiagonalMap (q : HillMeanZeroSource) : HillSignedComplexTarget :=
  WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))
    (hillHminusNativeDiagonalMap q.val)

theorem hillMeanZeroDiagonalMap_coe (q : HillMeanZeroSource) :
    (hillMeanZeroDiagonalMap q).val = hillHminusNativeDiagonalMap q.val :=
  WeightedCoeff.zeroModeProjection_coe _ _ (hillHminusNativeDiagonalMap_zero_mode _)

theorem analyticOnNhd_hillMeanZeroDiagonalMap :
    AnalyticOnNhd ℂ hillMeanZeroDiagonalMap hillMeanZeroComplexDomain := by
  intro q hq
  exact ((WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))).analyticAt _).comp
    ((analyticOnNhd_hillHminusNativeDiagonalMap _ hq).comp
      ((WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.analyticAt q))

theorem fderiv_hillMeanZeroDiagonalMap_eq_comp (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) :
    fderiv ℂ hillMeanZeroDiagonalMap q =
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).comp
        ((fderiv ℂ hillHminusNativeDiagonalMap q.val).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) := by
  exact ((WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).hasFDerivAt.comp q
    ((analyticOnNhd_hillHminusNativeDiagonalMap q.val hq).differentiableAt.hasFDerivAt.comp q
      (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.hasFDerivAt)).fderiv

def hillMeanZeroOffIndexJacobianRemainder (q : HillMeanZeroSource) :
    HillMeanZeroSource →L[ℂ] HillSignedComplexTarget :=
  fderiv ℂ hillMeanZeroComplexMap q -
    (WeightedCoeff.zeroModeExponentialSymbolEquiv (Weight.signedSobolev (-1/2))
      (hillHminusSignedOffIndexExponent q.val)).toContinuousLinearMap.comp
        (fderiv ℂ hillMeanZeroDiagonalMap q)

theorem hillMeanZeroOffIndexJacobianRemainder_eq_comp (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) :
    hillMeanZeroOffIndexJacobianRemainder q =
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))).comp
        ((hillHminusOffIndexJacobianRemainder q.val).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) := by
  apply ContinuousLinearMap.ext
  intro h
  simp only [hillMeanZeroOffIndexJacobianRemainder,sub_apply,
    ContinuousLinearMap.comp_apply,fderiv_hillMeanZeroComplexMap_eq_comp q hq,
    fderiv_hillMeanZeroDiagonalMap_eq_comp q hq,hillHminusOffIndexJacobianRemainder]
  change WeightedCoeff.zeroModeProjection _ ((fderiv ℂ hillHminusNativeComplexMap q.val) h.val) -
    WeightedCoeff.zeroModeExponentialSymbolEquiv _ (hillHminusSignedOffIndexExponent q.val)
      (WeightedCoeff.zeroModeProjection _ ((fderiv ℂ hillHminusNativeDiagonalMap q.val) h.val)) =
    WeightedCoeff.zeroModeProjection _ (((fderiv ℂ hillHminusNativeComplexMap q.val) h.val) -
      WeightedCoeff.exponentialSymbolEquiv _ (hillHminusSignedOffIndexExponent q.val)
        ((fderiv ℂ hillHminusNativeDiagonalMap q.val) h.val))
  rw [map_sub,WeightedCoeff.zeroModeProjection_exponentialSymbolEquiv]

theorem isCompactOperator_hillMeanZeroOffIndexJacobianRemainder (q : HillMeanZeroSource)
    (hq : q ∈ hillMeanZeroComplexDomain) :
    IsCompactOperator (hillMeanZeroOffIndexJacobianRemainder q) := by
  rw [hillMeanZeroOffIndexJacobianRemainder_eq_comp q hq]
  exact ((isCompactOperator_hillHminusOffIndexJacobianRemainder q.val hq).comp_clm
    (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL).clm_comp
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2)))

end NLS.KdV
