import NLS.KdV.HillRealCoordinateNontrivial
import NLS.KdV.HillNativeGardnerCoordinates
import NLS.KdV.HillRealSpatialTranslationContinuity
import NLS.FunctionalAnalysis.LinearSourceDerivative

/-! The actual physical native coordinate and its FREE spatial
linearization, with the original positive2*pi*n frequency. -/
noncomputable section
open Complex
namespace NLS.KdV

theorem hillRealPositiveCoordinate_eq_native (n : ℕ+) (q : HillRealMeanZeroSource) :
    hillRealPositiveCoordinate n q=hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q) := by
  rw [hillRealPositiveCoordinate,hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]
  rfl

/-- The derivative at zero retains the EXACT original spatial frequency. -/
theorem fderiv_hillRealPositiveCoordinate_spatialTranslation_zero (n : ℕ+) (s : ℝ)
    (h : HillRealMeanZeroSource) :
    (fderiv ℝ (fun q => hillRealPositiveCoordinate n (hillRealSpatialTranslation s q)) 0) h=
      exp ((s*(2*Real.pi*(n:ℕ)):ℝ)*I)*(fderiv ℝ (hillRealPositiveCoordinate n) 0) h := by
  have hc := (analyticAt_hillRealPositiveCoordinate n (hillRealSpatialTranslation s 0)).differentiableAt
  have hd := @NLS.FunctionalAnalysis.fderiv_clm_comp_apply ℝ
    HillRealMeanZeroSource HillRealMeanZeroSource ℂ
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (hillRealPositiveCoordinate n) (hillRealSpatialTranslation s) 0 h hc
  rw [map_zero,fderiv_hillRealPositiveCoordinate_zero_apply] at hd
  rw [hd,fderiv_hillRealPositiveCoordinate_zero_apply]
  have he : (hillRealSpatialTranslation s h).val.val.val (n:ℤ)=
      exp ((s*(2*Real.pi*(n:ℕ)):ℝ)*I)*h.val.val.val (n:ℤ) := by
    change (hillRealMeanZeroInclusion (hillRealSpatialTranslation s h)).val (n:ℤ)= _
    rw [hillRealSpatialTranslation_inclusion,WeightedCoeff.spatialTranslation_apply]
    rfl
  rw [he]
  ring

end NLS.KdV
