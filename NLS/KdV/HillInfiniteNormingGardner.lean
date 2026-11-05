import NLS.KdV.HillInfiniteNormingGradients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem norming_spatial_pairing_zero (q : RealPeriodOneHillPotential) (i j : ℕ) :
    unitComplexCurvePairing (hillLogNormingGradientCurve q (i+1) (by omega))
      (hillLogNormingGradientSpatialCurve q (j+1) (by omega))=0 := by
  have he : unitComplexCurvePairing (hillLogNormingGradientCurve q (i+1) (by omega))
      (hillLogNormingGradientSpatialCurve q (j+1) (by omega))=
      hillLogNormingGardnerBracket q (i+1) (j+1) (by omega) (by omega) := by
    rw [unitComplexCurvePairing_apply,hillLogNormingGardnerBracket]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillLogNormingGradientCurve q (j+1) (by omega)] with x hx
    rw [hx.deriv]
    rfl
  exact he.trans (hillLogNormingGardnerBracket_eq_zero q (i+1) (j+1) (by omega) (by omega))

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Actual infinite physical norming combinations commute under the genuine
Gardner derivative integral. Both cotangents and their spatial derivatives
are proved to converge, and the actual derivative is used in the bracket. -/
theorem hillInfiniteNormingGradient_GardnerBracket_eq_zero
    (q : RealPeriodOneHillPotential) (c d : ℕ → ℂ)
    (hc : Summable (fun j => ‖c j‖)) (hd : Summable (fun j => ‖d j‖)) :
    (∫ x in (0 : ℝ)..1,extend (hillInfiniteNormingGradient q c) x*
      deriv (extend (hillInfiniteNormingGradient q d)) x)=0 := by
  have hcs := (hillNormingGradientSeries_norm_summable h0q h0r q c hc).1.of_norm
  have hds := (hillNormingGradientSeries_norm_summable h0q h0r q d hd).2.of_norm
  have he : (∫ x in (0 : ℝ)..1,extend (hillInfiniteNormingGradient q c) x*
      deriv (extend (hillInfiniteNormingGradient q d)) x)=
      unitComplexCurvePairing (hillInfiniteNormingGradient q c) (hillInfiniteNormingGradientSpatial q d) := by
    rw [unitComplexCurvePairing_apply]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillInfiniteNormingGradient h0q h0r q d hd] with x hx
    rw [hx.deriv]
    rfl
  rw [he]
  have hrow (i : ℕ) : unitComplexCurvePairing (hillLogNormingGradientCurve q (i+1) (by omega))
      (hillInfiniteNormingGradientSpatial q d)=0 := by
    rw [hillInfiniteNormingGradientSpatial,
      (unitComplexCurvePairing (hillLogNormingGradientCurve q (i+1) (by omega))).map_tsum hds]
    simp only [map_smul,smul_eq_mul,norming_spatial_pairing_zero,mul_zero,tsum_zero]
  change (unitComplexCurvePairing.flip (hillInfiniteNormingGradientSpatial q d))
    (∑' i : ℕ,c i • hillLogNormingGradientCurve q (i+1) (by omega))=0
  rw [(unitComplexCurvePairing.flip (hillInfiniteNormingGradientSpatial q d)).map_tsum hcs]
  simp only [map_smul,smul_eq_mul,ContinuousLinearMap.flip_apply,hrow,mul_zero,tsum_zero]

end NLS.KdV
