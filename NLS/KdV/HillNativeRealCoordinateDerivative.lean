import NLS.KdV.HillNativeRealDerivative
import NLS.KdV.HillDirichletSpectralLocalFlow
import NLS.KdV.HillNativeMeanZeroDerivative

/-! The actual physical real native derivative evaluated at a raw signed
coordinate is the SAME full ambient complex coordinate derivative. -/
noncomputable section
namespace NLS.KdV

theorem fderiv_hillRealSignedMap_coordinate (q h : HillRealMeanZeroSource) (k : ℤ) :
    ((fderiv ℝ hillRealSignedMap q) h).val.val.val k=
      (fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion q)) (hillRealMeanZeroInclusion h) := by
  have he := congrArg (fun z : HillSignedComplexTarget => z.val.val k) (fderiv_hillRealSignedMap_coe q h)
  change ((fderiv ℝ hillRealSignedMap q) h).val.val.val k=
    ((fderiv ℂ hillMeanZeroComplexMap q.val) h.val).val.val k at he
  rw [fderiv_hillMeanZeroComplexMap_coordinate q.val (real_mem_hillMeanZeroComplexDomain q.val q.property) h.val k] at he
  exact he

end NLS.KdV
