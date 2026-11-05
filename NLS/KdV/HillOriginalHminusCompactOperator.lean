import NLS.KdV.HillOriginalHminusCompactness
import NLS.KdV.HillOriginalSequencePhysicalDifferential
import NLS.KdV.HillOriginalMeanZeroSpectralDerivative
import NLS.SequenceSpaces.CompactRowMajorant

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- The LITERAL original even-index inclusion from original complex L2
into native H-minus-one is a compact operator. -/
theorem isCompactOperator_hillOriginalHminusSource :
    IsCompactOperator hillOriginalHminusSource := by
  let S := WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2
  let T := S.toContinuousLinearEquiv.toContinuousLinearMap.comp hillOriginalHminusSource
  have hT : IsCompactOperator T := by
    apply Coeff.isCompactOperator_of_rowMajorant (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) T inverseBracketCoefficients
    intro k h
    have hh : ‖h.val (2*k)‖ ≤ ‖h‖ := by
      simpa only [SpectralWeight.toCoeff_apply] using
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (SpectralWeight.one.toCoeff h) (2*k)).trans
          (SpectralWeight.norm_toCoeff_le _ _)
    change ‖(Weight.sobolev (-1) k : ℂ)*(hillOriginalHminusSource h).val k‖ ≤ _
    rw [hillOriginalHminusSource_apply,norm_mul,norm_inverseBracketCoefficients_apply]
    simp only [Weight.sobolev_apply,Real.rpow_neg_one,norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (1+|(k : ℝ)|)⁻¹)]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hC := hT.clm_comp S.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he : S.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp T = hillOriginalHminusSource := by
    ext h
    exact S.symm_apply_apply _
  change IsCompactOperator (S.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp T) at hC
  rw [he] at hC
  exact hC

/-- The SAME original inclusion is compact on its actual real Banach domain. -/
theorem isCompactOperator_hillOriginalRealHminusInclusion :
    IsCompactOperator hillOriginalRealHminusInclusion := by
  have hc : IsCompactOperator (hillOriginalHminusSource.restrictScalars ℝ) :=
    isCompactOperator_hillOriginalHminusSource
  exact hc.comp_clm hillRealSourceSubmodule.subtypeL

/-- Compactness also holds after the literal original mean-zero restriction. -/
theorem isCompactOperator_hillOriginalMeanZeroHminusInclusion :
    IsCompactOperator (hillOriginalRealHminusInclusion.comp hillRealMeanZeroSourceSubmodule.subtypeL) :=
  isCompactOperator_hillOriginalRealHminusInclusion.comp_clm hillRealMeanZeroSourceSubmodule.subtypeL

end NLS.KdV
