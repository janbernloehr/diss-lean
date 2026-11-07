import NLS.Articles.KdVPseudomeasures.OriginalHillJacobianDenseRange
import NLS.KdV.HillNativeOffIndexCompact

/-! Actual compact off-index derivative correction at every original
physical Hminus-one potential, including arbitrary collapsed gaps.
The remaining diagonal derivative is not yet proved Fredholm. -/
noncomputable section
open NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_offIndex_Jacobian_compact (q : OriginalHminusOnePotential) :
    IsCompactOperator (hillHminusOffIndexJacobianRemainder (originalPeriodOneCoefficients q)) :=
  isCompactOperator_hillHminusOffIndexJacobianRemainder _
    (real_mem_hillHminusActionAngleNativeDomain _ (originalPeriodOneCoefficients_real q))

theorem original_Hill_meanZero_offIndex_Jacobian_compact (q : OriginalHminusOnePotential) :
    IsCompactOperator (fderiv ℂ hillMeanZeroComplexMap (originalHillRealMeanZeroSource q).val -
      (WeightedCoeff.zeroModeExponentialSymbolEquiv (Weight.signedSobolev (-1/2))
        (hillHminusSignedOffIndexExponent (originalHillRealMeanZeroSource q).val.val)).toContinuousLinearMap.comp
          (fderiv ℂ hillMeanZeroDiagonalMap (originalHillRealMeanZeroSource q).val)) :=
  isCompactOperator_hillMeanZeroOffIndexJacobianRemainder _
    (real_mem_hillMeanZeroComplexDomain _ (originalHillRealMeanZeroSource q).property)

theorem original_Hill_diagonal_coordinates (q : OriginalHminusOnePotential) (n : ℕ+) :
    (hillHminusNativeDiagonalMap (originalPeriodOneCoefficients q)).val ((n:ℕ):ℤ) =
      hillHminusCanonicalActionAmplitude n (originalPeriodOneCoefficients q)*
        hillHminusDiagonalCartesianMinus n (originalPeriodOneCoefficients q)/(Real.sqrt 2:ℂ) ∧
    (hillHminusNativeDiagonalMap (originalPeriodOneCoefficients q)).val (-((n:ℕ):ℤ)) =
      hillHminusCanonicalActionAmplitude n (originalPeriodOneCoefficients q)*
        hillHminusDiagonalCartesianPlus n (originalPeriodOneCoefficients q)/(Real.sqrt 2:ℂ) := by
  have hq := real_mem_hillHminusActionAngleNativeDomain _ (originalPeriodOneCoefficients_real q)
  exact ⟨hillHminusNativeDiagonalMap_positive _ hq n,hillHminusNativeDiagonalMap_negative _ hq n⟩

end NLS.Articles.KdVPseudomeasures
