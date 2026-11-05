import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerCanonicalTimeDerivative
import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerFreeDerivative
import NLS.KdV.HillNativeRealCoordinateDerivative

/-! The genuine strong canonical source tangent has the EXACT full
ambient rough native-coordinate velocity at EVERY signed index. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff NLS.LpSequence
namespace NLS.Articles.KdVPseudomeasures

theorem hillIntegerSobolevEquiv_eq_nativeCoordinate_at_order (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 N)) (k : ℤ) :
    ((hillIntegerSobolevEquiv N).equiv q).val.val.val k=
      hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (hillIntegerSourceInclusion N q)) := by
  rw [hillIntegerSobolevEquiv_apply]
  change (hillRealSignedMap (hillIntegerSourceInclusion N q)).val.val.val k=_
  rw [hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]
  rfl

theorem hillIntegerCanonicalKdVVector_rough_native_velocity (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 (N+3))) (k : ℤ) :
    (fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion (N+3) q)))
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion N (hillIntegerCanonicalKdVVector N q)))=
        I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion (N+3) q)) k:ℂ)*
          hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (hillIntegerSourceInclusion (N+3) q)) := by
  have he := congrArg (fun z => z.val.val.val k) (fderiv_hillIntegerSobolevEquiv_inclusion N
    (hillIntegerSourceOrderInclusion N (N+3) (by omega) q) (hillIntegerCanonicalKdVVector N q))
  rw [hillIntegerTargetInclusion_apply,fderiv_hillRealSignedMap_coordinate,
    hillIntegerSourceOrderInclusion_rough] at he
  rw [← he,hillIntegerCanonicalKdVVector_nativeJacobian,hillIntegerCanonicalNativeVelocity_apply,
    hillIntegerSobolevEquiv_eq_nativeCoordinate_at_order]

end NLS.Articles.KdVPseudomeasures
