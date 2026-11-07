import NLS.KdV.HillFractionalNativeRealization
import NLS.KdV.HillL2NativeComplexOneSmoothing
import NLS.FunctionalAnalysis.CoordinateDerivativeCompatibility
import NLS.SequenceSpaces.SobolevHomogeneous

/-! Literal compatibility of the fractional native Fourier derivative
with its rough endpoint and its actual L2 one-smoothing realization. -/
noncomputable section
open Filter Topology NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.KdV

def hillHminusFourierDefect (q : PeriodOneHminusOne) :
    WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  hillHminusNativeComplexMap q-halfFourierEquiv 2 q

theorem analyticAt_hillHminusFourierDefect (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : AnalyticAt ℂ hillHminusFourierDefect q :=
  (analyticOnNhd_hillHminusNativeComplexMap q (real_mem_hillHminusActionAngleNativeDomain q hq)).sub
    ((halfFourierEquiv 2).analyticAt q)

theorem fractionalFourierDefect_fderiv_rough (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q h : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : IsRealPeriodOneHminusOne (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) (k : ℤ) :
    (fderiv ℂ (hillFractionalFourierDefect r hr hr1) q h).val k =
      (fderiv ℂ hillHminusFourierDefect
        (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)
        (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) h)).val k := by
  apply clm_fderiv_eq_of_compatible_coordinates hillHminusFourierDefect
    (hillFractionalFourierDefect r hr hr1) (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith))
    (evalCLM _ 2 k) (evalCLM _ 2 k) q
    (analyticAt_hillHminusFourierDefect _ hq).differentiableAt
    (analyticAt_hillFractionalFourierDefect r hr hr1 q hq).differentiableAt _ h
  filter_upwards [(hillFractionalNativeRealization_local r hr hr1 q hq).2] with a ha
  change (hillFractionalFourierDefect r hr hr1 a).val k =
    (hillHminusFourierDefect (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) a)).val k
  simp only [hillFractionalFourierDefect, hillHminusFourierDefect, sub_val,
    negativeSobolevHalfFourierEquiv_apply, halfFourierEquiv_apply, sobolevInclusion_apply, ha]

theorem fractionalInclusion_l2 (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev 0) 2) :
    sobolevInclusion (show (-1:ℝ) ≤ -r by linarith)
      (sobolevInclusion (show -r ≤ 0 by linarith) q) =
        periodOneL2Inclusion (sobolevToL2 (by norm_num) q) := by
  apply Subtype.ext
  funext k
  simp only [sobolevInclusion_apply, periodOneL2Inclusion_apply, sobolevToL2_apply]

theorem fractionalFourierDefect_fderiv_l2 (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q h : WeightedCoeff (Weight.sobolev 0) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneL2Inclusion (sobolevToL2 (by norm_num) q))) (k : ℤ) :
    (fderiv ℂ (fun a : WeightedCoeff (Weight.sobolev 0) 2 =>
      hillL2NativeComplexFourierRemainder (sobolevToL2 (by norm_num) a)) q h).val k =
      (fderiv ℂ (hillFractionalFourierDefect r hr hr1)
        (sobolevInclusion (show -r ≤ 0 by linarith) q)
        (sobolevInclusion (show -r ≤ 0 by linarith) h)).val k := by
  let T : WeightedCoeff (Weight.sobolev 0) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-r)) 2 :=
    sobolevInclusion (show -r ≤ 0 by linarith)
  have hqT : IsRealPeriodOneHminusOne
      (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) (T q)) := by
    rw [fractionalInclusion_l2 r hr hr1]
    exact hq
  have hF := analyticAt_hillFractionalFourierDefect r hr hr1 (T q) hqT
  have hG := (analyticAt_hillL2NativeComplexFourierRemainder _ hq).comp
    ((sobolevToL2 (by norm_num : (0:ℝ) ≤ 0)).analyticAt q)
  apply clm_fderiv_eq_of_compatible_coordinates (hillFractionalFourierDefect r hr hr1)
    (fun a : WeightedCoeff (Weight.sobolev 0) 2 => hillL2NativeComplexFourierRemainder
      (sobolevToL2 (by norm_num) a)) T (evalCLM _ 2 k) (evalCLM _ 2 k)
      q hF.differentiableAt hG.differentiableAt _ h
  have hs := (T.continuous.tendsto q).eventually
    (hillFractionalNativeRealization_local r hr hr1 (T q) hqT).2
  have hl := ((sobolevToL2 (by norm_num : (0:ℝ) ≤ 0)).continuous.tendsto q).eventually
    (eventually_hillL2NativeComplexFourierRemainder_apply _ hq)
  filter_upwards [hs,hl] with a ha hb
  change (hillL2NativeComplexFourierRemainder (sobolevToL2 (by norm_num) a)).val k =
    (hillFractionalFourierDefect r hr hr1 (T a)).val k
  rw [hb k, hillFractionalFourierDefect, sub_val, ha k,
    negativeSobolevHalfFourierEquiv_apply, fractionalInclusion_l2 r hr hr1,
    sobolevInclusion_apply, sobolevToL2_apply]

end NLS.KdV
