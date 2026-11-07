import NLS.KdV.HillNativeRealSignedMap
import NLS.KdV.HillDirichletSpectralLocalFlow
import NLS.KdV.HillNativeGardnerCoordinates

/-! Actual raw signed coefficients of the genuine physical real native
map are the same ambient complex native scalar functions. -/
noncomputable section
namespace NLS.KdV

theorem hillRealSignedMap_apply_nativeCoordinate (q : HillRealMeanZeroSource) (k : ℤ) :
    (hillRealSignedMap q).val.val.val k=hillHminusNativeCoordinate k (hillRealMeanZeroInclusion q) := by
  rw [hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]
  rfl

end NLS.KdV
