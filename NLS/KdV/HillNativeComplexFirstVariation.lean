import NLS.KdV.HillNativeComplexCoordinates
import NLS.KdV.HillNativeCartesianFirstVariation
import NLS.RealAnalysis.FourierSquareRootNormalization

/-! The FULL native signed complex Banach derivative is the weighted
Fourier transform on the complex mean-zero tangent, with its exact constant. -/
noncomputable section
open Set Complex NLS.RealAnalysis
namespace NLS.KdV

theorem fderiv_hillHminusNativeComplexMap_zero :
    fderiv ℂ hillHminusNativeComplexMap 0=
      (WeightedCoeffPair.signedCartesianCLM (-1/2)).comp (fderiv ℂ hillHminusNativeCartesianMap 0) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hd := (WeightedCoeffPair.signedCartesianCLM (-1/2)).hasFDerivAt.comp 0
    (analyticOnNhd_hillHminusNativeCartesianMap 0
      (real_mem_hillHminusActionAngleNativeDomain 0 hr)).differentiableAt.hasFDerivAt
  exact hd.fderiv

theorem fderiv_hillHminusNativeComplexMap_positive_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    ((fderiv ℂ hillHminusNativeComplexMap 0) h).val ((n:ℕ):ℤ)=
      h.val (n:ℤ)/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) := by
  have hn : (0:ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  rw [fderiv_hillHminusNativeComplexMap_zero,ContinuousLinearMap.comp_apply,
    WeightedCoeffPair.signedCartesianCLM_positive _ _ _ hn,
    (fderiv_hillHminusNativeCartesianMap_positive_mean_zero n h hh).1,
    (fderiv_hillHminusNativeCartesianMap_positive_mean_zero n h hh).2,
    complex_sqrt_two_pi_mul_nat]
  field_simp
  ring

theorem fderiv_hillHminusNativeComplexMap_negative_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    ((fderiv ℂ hillHminusNativeComplexMap 0) h).val (-((n:ℕ):ℤ))=
      h.val (-(n:ℤ))/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) := by
  have hn : (0:ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  rw [fderiv_hillHminusNativeComplexMap_zero,ContinuousLinearMap.comp_apply,
    WeightedCoeffPair.signedCartesianCLM_negative _ _ _ hn,
    (fderiv_hillHminusNativeCartesianMap_positive_mean_zero n h hh).1,
    (fderiv_hillHminusNativeCartesianMap_positive_mean_zero n h hh).2,
    complex_sqrt_two_pi_mul_nat]
  field_simp
  ring

theorem fderiv_hillHminusNativeComplexMap_zero_mode (h : PeriodOneHminusOne) :
    ((fderiv ℂ hillHminusNativeComplexMap 0) h).val 0=0 := by
  rw [fderiv_hillHminusNativeComplexMap_zero,ContinuousLinearMap.comp_apply,
    WeightedCoeffPair.signedCartesianCLM_zero]

end NLS.KdV
