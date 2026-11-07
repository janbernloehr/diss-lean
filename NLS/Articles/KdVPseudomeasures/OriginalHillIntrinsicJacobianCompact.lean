import NLS.Articles.KdVPseudomeasures.OriginalHillOffIndexJacobianCompact
import NLS.KdV.HillMeanZeroIntrinsicCompact

/-! Actual normalized-amplitude compactness and the intrinsic
diagonal reduction at every original physical Hminus-one source.
The intrinsic diagonal Fourier remainder remains a proof obligation. -/
noncomputable section
open NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_normalized_amplitude_Jacobian_compact (q : OriginalHminusOnePotential) :
    IsCompactOperator (fderiv ℂ hillMeanZeroDiagonalMap (originalHillRealMeanZeroSource q).val-
      fderiv ℂ hillMeanZeroIntrinsicDiagonalMap (originalHillRealMeanZeroSource q).val) :=
  isCompactOperator_hillMeanZeroAmplitudeJacobianDifference _
    (real_mem_hillMeanZeroComplexDomain _ (originalHillRealMeanZeroSource q).property)

theorem original_Hill_intrinsic_Jacobian_remainder_compact (q : OriginalHminusOnePotential) :
    IsCompactOperator (hillMeanZeroIntrinsicJacobianRemainder (originalHillRealMeanZeroSource q).val) :=
  isCompactOperator_hillMeanZeroIntrinsicJacobianRemainder _
    (real_mem_hillMeanZeroComplexDomain _ (originalHillRealMeanZeroSource q).property)

theorem original_Hill_intrinsic_diagonal_coordinates (q : OriginalHminusOnePotential) (n : ℕ+) :
    (hillHminusIntrinsicDiagonalMap (originalPeriodOneCoefficients q)).val ((n:ℕ):ℤ) =
      hillHminusDiagonalCartesianMinus n (originalPeriodOneCoefficients q)/
        (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) ∧
    (hillHminusIntrinsicDiagonalMap (originalPeriodOneCoefficients q)).val (-((n:ℕ):ℤ)) =
      hillHminusDiagonalCartesianPlus n (originalPeriodOneCoefficients q)/
        (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) := by
  have hq := real_mem_hillHminusActionAngleNativeDomain _ (originalPeriodOneCoefficients_real q)
  exact ⟨hillHminusIntrinsicDiagonalMap_positive _ hq n,hillHminusIntrinsicDiagonalMap_negative _ hq n⟩

end NLS.Articles.KdVPseudomeasures
